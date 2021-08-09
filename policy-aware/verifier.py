from topo import *
import sys
import getopt
from z3 import *
import pickle
import gc
import threading
import ctypes
import random



class Usage(Exception):
    def __init__(self, msg):
        self.msg = msg

# This is the latest version: JUly 3th 2019
# We try to implement the paper version.
# We implement local preference for each record.
# Work for all possible policies
# local preference range: customer (1, 2); peer (2, 3, 4, 5); provider (5, 6, 7); ???


#
class Verifier:
    def __init__(self, opts, args, flag = True, fakenum = 0, violateexport = 0.0, violateimport = 0.0):
#        t1 = Tactic("simplify")
#        t2 = Tactic("propagate-values")
#        t3 = Tactic("solve-eqs")
#        t4 = Tactic("bit-blast")
#        t5 = Tactic("smt")
#        self.solver = Then(t1, t2, t3, t4, t5).solver()

        self.solver = Solver()
#        z3.set_option(unsat_core=True)
        self.topo = None
        for opt, arg in opts:
            if opt == "-r":
                # read AS relationship from CAIDA file
                self.topo = Topo(arg, fakenum = fakenum, violateexport = violateexport, violateimport = violateimport)

                print "start generate special policy"
                # generate sp ecial policies, PeerBoost, in the AS topology:
                self.topo.gen_PB(flag)
                print "finish generate special policy"

                #based on topology and policy, generate announcement graph
                self.topo.buildgraph()

    # clear the state to original state
    def clear(self):
        self.solver = Solver()
        self.topo.clear()

    def setupleaves(self):
        self.solver.add(And(self.topo.setupleaves()))

    def setwaypoint(self, attacker):
        # set the attacker AS as the waypoint target
        asnode = self.topo.dict[attacker]
        asnode.iswaypoint = True

    def isselected(self, node):
        # return whether the node is selected after trim
        return self.topo.selected(node)

    def setATTACKER(self, att):
        self.topo.dict[att].isattacker = True

    def addexport_without(self, withouts, link_break = False):
        for asid, node in self.topo.dict.iteritems():
            if asid not in withouts:
                self.solver.add(node.exportconstraints(self.topo.dict, self.topo.ASNUM, link_break))

    def setup_ITE_neighbor(self, dest, opt = False, selected_neighbor = 0):
        node = self.topo.dict[dest]
        self.solver.add(node.exportconstraints_prepend(self.topo.dict, self.topo.ASNUM, opt = opt,
                                                       selected_neighbor = selected_neighbor))

    # translate export policies and add into solver
    def addexport(self, link_break = False):
        for asid, node in self.topo.dict.iteritems():
            if not node.isattacker:
                self.solver.add(node.exportconstraints(self.topo.dict, self.topo.ASNUM, link_break))


    def addimport_without(self, withouts):
        for asid, node in self.topo.dict.iteritems():
            if not node.origin and asid not in withouts:
                self.solver.add(node.importconstraints(self.topo.dict, self.topo.ASNUM))

    def addimport_bgp(self, ases):
        for asid, node in self.topo.dict.iteritems():
            #if not node.isattacker and not node.origin:
            if asid in ases:
                self.solver.add(node.importconstraints_bgp(self.topo.dict, self.topo.ASNUM))

    # translate import policies and add into solver
    def addimport(self):
        for asid, node in self.topo.dict.iteritems():
            #if not node.isattacker and not node.origin:
            if not node.origin:
                self.solver.add(node.importconstraints(self.topo.dict, self.topo.ASNUM))


    def devideproperty(self, aspath, asnum, attindex, power):
        num = asnum ** power
        return (aspath / num) % asnum == attindex

    # the victim uses a best route going through the attacker
    def checkwaypoint(self, victim, attacker):
        victimnet = self.topo.dict[victim]
        self.solver.add(victimnet.best.flag == True)

    #victim has best route
    def property_hasroute(self, victim):
        self.solver.add(self.topo.dict[victim].best.valid == True)

    def property_allhasroute(self):
        p = []
        for id, net in self.topo.dict.iteritems():
            p.append(net.best.valid == True)
        self.solver.add(Not(And(p)))
        #self.property_hasroute(id)


    def addproperty(self, victim, attacker):
        # add property to check traffic attraction
        # whether the best route of victim goes through attacker?
        attindex = self.topo.dict[attacker].index
        victimnet = self.topo.dict[victim]
        orlist = []
        for i in range(0,10):
            orlist.append(self.devideproperty(victimnet.best.aspath, self.topo.ASNUM, attindex, i))
#        property = Or(victimnet.best.aspath % self.topo.ASNUM == attindex, (victimnet.best.aspath / self.topo.ASNUM) % self.topo.ASNUM == attindex)
        self.solver.add(Or(orlist))


def printresult(s):
    list = []
    for d in s.model().decls():
        list.append("%s = %s" % (d.name(), s.model()[d]))
    list.sort()
    count = 0
    for d in list:
        print d
        count += 1
        if count % 6 == 0:
            print "\n"

# alltrim used for ibgp
def gen_rsys(opts, args, ORIGIN, VICTIM, ATTACKER, rsys = None, calprovider = False, stat = None, trim = True,
             alltrim = False, policyaware = False, violateexport = 0.0, violateimport = 0.0):
    localtime = time.asctime(time.localtime(time.time()))
    print "start initialize verifier", localtime
    #    sys.setrecursionlimit(65535)
    # initialize verifier. False means no special policy generation
    if rsys == None:
        rsys = Verifier(opts, args, False, violateexport = violateexport, violateimport = violateimport)
        if calprovider:
            localtime = time.asctime(time.localtime(time.time()))
            print "compute provider cone start", localtime
            rsys.topo.computeprovidercone()
            localtime = time.asctime(time.localtime(time.time()))
            print "compute provider cone end", localtime
    else:
        t1 = time.time()
        rsys.clear()
        t2 = time.time()
        if stat:
            stat["cleartime"] = t2 - t1

    localtime = time.asctime(time.localtime(time.time()))
    print "finish initialize verifier", localtime

    # !!!!! set waypoint for ATTACKER
    if ORIGIN != ATTACKER:
        rsys.setwaypoint(ATTACKER)

    # set up origin (should before import constraints)
    # when ORIGIN == ATTACKER, there is no attacker
    #    ORIGIN = 1
    #    ATTACKER = 1
    #    VICTIM = 25
    rsys.solver.add(rsys.topo.selectorigin(ORIGIN))
    #    rsys.topo.selectattacker(ATTACKER)

    localtime = time.asctime(time.localtime(time.time()))
    
    print "start topotrim", localtime
    # origin, victim, attacker
    t1 = time.time()
    if not alltrim:
#        rsys.topo.topotrim(ORIGIN, VICTIM, ATTACKER, trim = trim)
        rsys.topo.topotrim_new([ORIGIN,ATTACKER], [VICTIM], trim = trim, policyaware = policyaware)
    else:
        for id, net in rsys.topo.dict.iteritems():
            rsys.topo.topotrim(ORIGIN, id, ORIGIN, trim = trim)
            for id, net in rsys.topo.dict.iteritems():
                if not net.unode.selected:
                    net.unode.visited = False
                if not net.dnode.selected:
                    net.dnode.visited = False

    t2 = time.time()
    if stat:
        stat["trimtime"] = t2 - t1
    localtime = time.asctime(time.localtime(time.time()))
    print "finish topotrim", localtime

    rsys.topo.trimstat()
    print ("Attacker:", ATTACKER, " neighbors.")
    rsys.topo.neighborstat(ATTACKER)

    # generate necessary records after dag trim
    t1 = time.time()
    rsys.topo.gen_records()
    t2 = time.time()
    if stat:
        stat["gen_records_time"] = t2 -t1

    localtime = time.asctime(time.localtime(time.time()))
    print "finish record generation trim.", localtime

    return rsys



def gen_bestroute(opts, args, inORIGIN, inVICTIM, trim = True, num = 0):
    states={}
    states["origin"] = inORIGIN

    rsys = gen_rsys(opts, args, inORIGIN, inVICTIM, inORIGIN, trim = trim)

    t1 = time.time()
    localtime = time.asctime(time.localtime(t1))
    print ("start generate constraints", localtime)
    # add export constraints
    rsys.addexport()
    # add import constraints
    rsys.addimport()

    # when it is not trimed, the leaves should be setup for valid#
    rsys.setupleaves()

    t2 = time.time()
    localtime = time.asctime(time.localtime(t2))
    print ("finish generate constraints", localtime)
    states["gen_constraints"] = t2 - t1


    # add traffic attraction property
    #    rsys.addproperty(VICTIM, ATTACKER)

    t1 = time.time()
    localtime = time.asctime(time.localtime(t1))
    print "start checking", localtime
    rst = rsys.solver.check()
    t2 = time.time()
    localtime = time.asctime(time.localtime(t2))
    print "result:", rst, localtime
    print rsys.solver.statistics()
    states["result"] = rst
    states["checking_time"] = t2 - t1
    states["dotrim"] = trim

    states["asnum"] = len(rsys.topo.dict)
    states["linknum"] = rsys.topo.relationnum

    print(states)

    with open("./stablestate_" + str(num) + ".txt", "w") as f:
        pickle.dump(states, f)

    if rst == sat:
    #    printresult(rsys.solver)
        # return
        print(rst)
    elif rst == unsat:
        print(rst)
#        for c in rsys.solver.assertions():
#            print c
    return rst


def waypoint_link_break(opts, args, ORIGIN, SOURCE, POINT):
    rsys = gen_rsys(opts, args, ORIGIN, SOURCE, ORIGIN)

    rsys.addexport(link_break=True)
    rsys.addimport()
    rsys.addproperty(SOURCE, POINT)

    if not rsys.isselected(POINT):
        print ("[waypoint_link_break]", POINT, " is not selected after trim.", SOURCE,  " will not use ", POINT)
        return

    localtime = time.asctime(time.localtime(time.time()))
    print "[waypoint_link_break] start checking", localtime
    rst = rsys.solver.check()
    localtime = time.asctime(time.localtime(time.time()))
    print "[waypoint_link_break] result:", rst, localtime
    print rsys.solver.statistics()
    if rst == sat:
        print ("[waypoint_link_break]", SOURCE, " might use ", POINT, " to reach ", ORIGIN)
        printresult(rsys.solver)
        # return
    elif rst == unsat:
        print ("[waypoint_link_break]", SOURCE, " will not use ", POINT, " to reach ", ORIGIN)
        for c in rsys.solver.assertions():
            print c
    return rst

def generatefaketopo(opts, args, num):
    rsys = Verifier(opts, args, False, fakenum = num)


def check_combination_opt(rsys, pset, qset, att):
    attacker = rsys.topo.dict[att]
    rsys.solver.push()
    rsys.solver.add(attacker.attackstrategy_combine_opt(rsys.topo.dict, rsys.topo.ASNUM, pset, qset))
    rst = rsys.solver.check()
    rsys.solver.pop()
    return rst

def check_combination(rsys, p, q, att):
    attacker = rsys.topo.dict[att]
    rsys.solver.push()
    # TODO
    rsys.solver.add(attacker.attackstrategy_combine(rsys.topo.dict, rsys.topo.ASNUM, p, q))
    rst = rsys.solver.check()
    rsys.solver.pop()
    return rst





# TRY ATTACK announcement one by one. and record the total verification time.
def veri_trafficattraction_allinone(opts, args, ORIGIN, VICTIM, ATTACKER, stat, rsys = None):
    rsys = gen_rsys(opts, args, ORIGIN, VICTIM, ATTACKER, rsys=rsys, calprovider= True)


    rsys.setATTACKER(ATTACKER)

        # add export constraints
    rsys.addexport()
        # add import constraints
    rsys.addimport()

        #       done in rsys
    rsys.checkwaypoint(VICTIM, ATTACKER)
        #        rsys.addproperty(VICTIM, ATTACKER)

    attacker = rsys.topo.dict[ATTACKER]

    rsys.solver.set("timeout", 600000)


    localtime = time.asctime(time.localtime(time.time()))
    print ("start to check", localtime)


    '''
    t1 = time.time()
    vnet = rsys.topo.dict[VICTIM]
    onet = rsys.topo.dict[ORIGIN]
    constant = vnet.providercone & (~onet.providercone)
    plist = []
    for p in rsys.topo.att_neighbors:
        # find potential t for all providers of the attacker
        pnet = rsys.topo.dict[p]
        rst = constant & pnet.providercone
        tlist = []
        for i in range(0, rsys.topo.ASNUMTotal):
            if rst[i] == 1:
                tlist.append(rsys.topo.providerindex2as[i].asid)
        selecteflag = False
        for t in tlist:
            tnet = rsys.topo.dict[t]
            if tnet.unode.selected or tnet.dnode.selected:
                selecteflag = True
                break
        if selecteflag:
            plist.append(p)

    t2 = time.time()
    '''

#    pset = set(plist)
#    qset = rsys.topo.att_allneighbors - pset

    pset = rsys.topo.att_allneighbors

    qset = set()

    totalt1 = time.time()

    rsys.solver.add(attacker.attackstrategy_allinone(rsys.topo.dict, rsys.topo.ASNUM, pset, qset))

    rst = rsys.solver.check()
#    rsys.solver.pop()

    totalt2 = time.time()
    stat["sumtimeallinone"] = totalt2 - totalt1

    localtime = time.asctime(time.localtime(time.time()))
    print ("finish the phase 1", localtime)

    stat["plist"] = pset
    stat["plist_num"] = len(pset)

    stat["resultallinone"] = rst
#        return rsys

#    print ("+++++++++++++++++++++++++++++++++++ find t++++++++++++++++++++++++++++++++++++++++", t2 - t1, " seconds")
#    stat["sumtime_findt"] = t2 - t1
    return rsys


def old_verify2(rsys, VICTIM, ORIGIN, stat):
    # just a backup function
    newresult = unsat
    findttime = 0

    if newresult == unsat and len(rsys.topo.att_neighbors) > 1:
        # find potential t
        print ("================================start find t ===================================================")

        t1 = time.time()
        pairlist = pairenumerate(rsys.topo.att_neighbors)
        t2 = time.time()
        findttime += t2 - t1
        print ("all neighbors pairs:", pairlist)
        t1 = time.time()
        flag = False
        vnet = rsys.topo.dict[VICTIM]
        onet = rsys.topo.dict[ORIGIN]
        constant = vnet.providercone & (~onet.providercone)
        t2 = time.time()
        findttime += t2 - t1
        for pair in pairlist:
            print ("for pair:", pair)
            t1 = time.time()
            pnet = rsys.topo.dict[pair[0]]
            qnet = rsys.topo.dict[pair[1]]
            rst = constant & (pnet.providercone & (~qnet.providercone))
            result = rst[0: rsys.topo.ASNUMTotal]
            t2 = time.time()
            findttime += t2 - t1
            #            print "result", result
            print "potential t:"
            tlist = []
            for i in range(0, rsys.topo.ASNUMTotal):
                if result[i] == 1:
                    tlist.append(rsys.topo.providerindex2as[i].asid)
                    flag = True
            print tlist
        print ("find t use ", findttime, " seconds.")
        print ("=================================finish find t =================================================")
        stat["findttime"] = findttime
        stat["existt"] = flag

def pairenumerate(neighbors):
    l = len(neighbors)
    neighborl = list(neighbors)
    tmp = []
    for i in range(0,l):
        for j in range(i + 1,l):
            tmp.append((neighborl[i], neighborl[j]))
            tmp.append((neighborl[j], neighborl[i]))
    return tmp

def veri_trafficattraction(opts, args, ORIGIN, VICTIM, ATTACKER, stat, rsys = None, trim = True, policyaware = False,
                           violateexport = 0.0, violateimport = 0.0):
#    stat = {"o": ORIGIN, "v": VICTIM, "a": ATTACKER}
    stat["o"] = ORIGIN
    stat["v"] = VICTIM
    stat["a"] = ATTACKER
    rsys = gen_rsys(opts, args, ORIGIN, VICTIM, ORIGIN, rsys = rsys, stat=stat, trim = trim, policyaware = policyaware,
                    violateexport = violateexport, violateimport = violateimport)

    stat["selected_AS1"] = rsys.topo.ASNUM
    stat["selected_node1"] = rsys.topo.selectednodesnum
    stat["selected_edge1"] = rsys.topo.selectededgenum

#   done in gen_rsys
    rsys.setwaypoint(ATTACKER)

    # add export constraints
    t1 = time.time()
    rsys.addexport()
    # if not trim, we need to setup leave announcement
#    if not trim:
    rsys.setupleaves()
    t2 = time.time()
    stat["addexporttime1"] = t2 - t1
    # add import constraints
    rsys.addimport()
    t1 = time.time()
    stat["addimporttime1"] = t1 - t2

    rsys.checkwaypoint(VICTIM, ATTACKER)

    rsys.property_hasroute(VICTIM)

#    rsys.addproperty(VICTIM, ATTACKER)




    localtime = time.asctime(time.localtime(time.time()))
    print "start checking", localtime
    t1 = time.time()
    rst = rsys.solver.set("timeout", 600000)
    rst = rsys.solver.check()
    t2 = time.time()
    stat["rt1"] = t2 - t1
    localtime = time.asctime(time.localtime(time.time()))
    print "result:", rst, localtime, t2 - t1
    stat["result1"] = rst

    if rst == sat:
        print "victim", VICTIM, " might use", ATTACKER, " to reach ORIGIN", ORIGIN, " in normal case.!!!!!!!!!!!!!!"
        stat["result2"] = rst
#        printresult(rsys.solver)
#        for c in rsys.solver.assertions():
#            print c
    else:
        print "Additional verification*******************************************************************************"
        rsys = gen_rsys(opts, args, ORIGIN, VICTIM, ATTACKER, rsys = rsys, trim = trim, policyaware = policyaware,
                        violateexport = violateexport, violateimport = violateimport)

        stat["selected_AS2"] = rsys.topo.ASNUM
        stat["selected_node2"] = rsys.topo.selectednodesnum
        stat["selected_edge2"] = rsys.topo.selectededgenum

        rsys.setATTACKER(ATTACKER)

#        rsys.setwaypoint(ATTACKER)

        # add export constraints
        t1 = time.time()
        rsys.addexport()
        # if not trim, we need to setup leave announcement
#        if not trim:
        rsys.setupleaves()
        t2 = time.time()
        stat["addexporttime2"] = t2 - t1
        # add import constraints
        rsys.addimport()
        t1 = time.time()
        stat["addimporttime2"] = t1 - t2


#       done in rsys
        rsys.checkwaypoint(VICTIM, ATTACKER)
#        rsys.addproperty(VICTIM, ATTACKER)
        rsys.property_hasroute(VICTIM)

        stat["announcement_num"] = rsys.topo.neighborstat(ATTACKER)

        localtime = time.asctime(time.localtime(time.time()))
        print "start the second checking", localtime
        rsys.solver.set("timeout", 600000)
        t1 = time.time()

        # add export constraints for attackers; put it here to be fair with comparing with one-by-one
        # add export constraints for attackers: announce any correct routes
        rsys.solver.add(rsys.topo.dict[ATTACKER].exportconstraints(rsys.topo.dict, rsys.topo.ASNUM, False))


        rst = rsys.solver.check()
        t2 = time.time()
        stat["rt2"] = t2 - t1
        localtime = time.asctime(time.localtime(time.time()))
        print "result:", rst, localtime, t2 - t1
        stat["result2"] = rst
        if rst == sat:
            print "Attacker", ATTACKER, " can sucessfully attract traffic from", VICTIM, " to", ORIGIN
#            printresult(rsys.solver)
        else:
            print "Attacker", ATTACKER, " can not sucessfully attract traffic from", VICTIM, " to", ORIGIN
            #for c in rsys.solver.assertions():
            #    print c
    return rsys



def multi_hijacking(opts, args, num, cands = None, outputsuffix = "", trim = True, policyaware = False,
                    violateexport = 0.0, violateimport = 0.0):
    v = Verifier(opts, args, False, violateexport = violateexport, violateimport = violateimport)
    keys = v.topo.dict.keys()
    print("start ", num, " times experiment")
    stats = []
    rsys = v
    if cands == None:
        cands = []
        for i in range(0, num):
            threenodes = set()
            while len(threenodes) < 3:
                key = random.choice(keys)
                if key not in threenodes:
                    threenodes.add(key)
            cands.append(list(threenodes))

    i = 0
    cands = cands[0:num]
    for threenodeslist in cands:
        print("===============================================the", i, "experiment===================================")
        gc.collect()
        stat = {}
        rsys = veri_trafficattraction(opts, args, threenodeslist[0], threenodeslist[2], threenodeslist[1],
                                      stat, rsys = rsys, trim = trim, policyaware = policyaware,
                                      violateexport = violateexport, violateimport = violateimport)
        print("stat:" + str(stat))
        stats.append(stat)
        gc.collect()
        f = open("hijacking_stats" + outputsuffix + ".txt", "wb")
        pickle.dump(stats, f)
        f.close()
        i += 1
    print(stats)
    for stat in stats:
        print stat


def multi_topo_hijacking(trim = True, smallscale = True, policyaware = False, violateexport = 0.0, violateimport = 0.0):
    cands = None
    if smallscale:
        for i in range(100, 500, 100):
            opts = [("-r", "../topos/small" + str(i) +  ".txt")]
            with open("../topos/hijack" + str(i) + ".txt") as cands:
                cands = pickle.load(cands)
                print ("start topo:" + str(i) + ":" + str(cands))
                if trim:
                    suffix = "_nogr_" + str(i) + "_" +str(violateexport).replace(".", "") + "_" + \
                             str(violateimport).replace(".","")
                else:
                    suffix = "_nogr_" + str(i) + "_notrim" + "_" + str(violateexport).replace(".", "") + "_" + \
                             str(violateimport).replace(".","")
                multi_hijacking(opts, None, 3, cands = cands, outputsuffix = suffix, trim = trim,
                                policyaware = policyaware, violateexport = violateexport, violateimport = violateimport)
    else:
        for i in range(2003, 2023, 5):
            opts = [("-r", "../topos/" + str(i) + "0501.as-rel.txt")]
            if trim:
                suffix = "_nogr_" + str(i)
            else:
                suffix="_nogr_" + str(i) + "_notrim"
            multi_hijacking(opts, None, 10, cands = cands, outputsuffix = suffix, trim = trim,
                            policyaware = policyaware, violatexport = violateexport, violateimport = violateimport)

def multiple_ite(trim = True, smallscale = True, policyaware = False, violateexport = 0.0, violateimport = 0.0):
    if smallscale:
        for i in range(100, 1100, 300):
            topofile = "../topos/15169small" + str(i) + ".txt"
            ifile = "../topos/15169ite" + str(i) + ".txt"
            if trim:
                ofile = "ite_stats_" + str(i) + ".txt"
            else:
                ofile = "ite_stats_" + str(i) + "_notrim.txt"
            opts = [("-r", topofile)]
            ITE_neighbor(opts, None, ifile = ifile , ofile = ofile, trim = trim, violateexport = violateexport,
                         violateimport = violateimport)
    else:
        for i in range(2018, 2023, 5):
            topofile = "../topos/" + str(i) + "0501.as-rel.txt"
            ifile = "../topos/15169_year" + str(i) + "ite.txt"
            if trim:
                ofile = "ite_stats_" + str(i) + ".txt"
            else:
                ofile = "ite_stats_" + str(i) + "_notrim.txt"
            opts = [("-r", topofile)]
            ITE_neighbor(opts, None, ifile=ifile, ofile=ofile, trim=trim, violateexport = violateexport,
                         violateimport = violateimport)


# find candidate for ITE_neighbors
def cand4ITEN(opts, args, num = 100):
    rst = {}
    rsys = Verifier(opts, args, False)
    VICTIM = 15169
    counter = 0
    for asid, node in rsys.topo.dict.iteritems():
        if asid != VICTIM and asid not in rsys.topo.dict[VICTIM].neighbors and len(node.neighbors) >= 2:
            ORIGIN = asid
            rsys.topo.topotrim(ORIGIN, VICTIM, ORIGIN)
            neighbors = []
            for n in node.neighbors:
                if rsys.isselected(n):
                    neighbors.append(n)
            rsys.topo.trimstat()
            rsys.clear()
            if len(neighbors) >= 2:
                rst[asid] = neighbors
                counter += 1
        if counter >= num:
            break
    print("ITE_neighbor candidate:", rst)
    with open("./ITE_n_candidate.txt", "w") as f:
        pickle.dump(rst, f)
    return rst


def rsys_init(opts, args, rsys = None, calprovider = False):
    # initialize verifier. False means no special policy generation
    if rsys == None:
        rsys = Verifier(opts, args, False)
        if calprovider:
            localtime = time.asctime(time.localtime(time.time()))
            print "compute provider cone start", localtime
            rsys.topo.computeprovidercone()
            localtime = time.asctime(time.localtime(time.time()))
            print "compute provider cone end", localtime
    else:
        rsys.clear()

    localtime = time.asctime(time.localtime(time.time()))
    print "finish initialize verifier", localtime
    return rsys

def check_ITE_src(opts, args, dest, neighbor, src, state, rsys = None, calprovider = False, opt = False):
    tag = " "
    if opt:
        tag = "_opt "
    print("*******************************************start ITE_src check", tag)
    localtime = time.asctime(time.localtime(time.time()))
    print "start initialize verifier", localtime
    #    sys.setrecursionlimit(65535)
    rsys = rsys_init(opts, args, rsys = rsys, calprovider = calprovider)



    rsys.setwaypoint(neighbor)

    # set up origin (should before import constraints)

    rsys.solver.add(rsys.topo.selectorigin(dest))

    localtime = time.asctime(time.localtime(time.time()))
    print "start topotrim", localtime
    # origin, victim, attacker
    rsys.topo.topotrim(dest, src, dest)
    localtime = time.asctime(time.localtime(time.time()))
    print "finish topotrim", localtime

    rsys.topo.trimstat()

    state["selected_node"] = rsys.topo.selectednodesnum
    state["selected_edge"] = rsys.topo.selectededgenum

    # generate necessary records after dag trim
    rsys.topo.gen_records()

    localtime = time.asctime(time.localtime(time.time()))
    print "finish record generation trim.", localtime

    # add export constraints
#    rsys.addexport_without([dest])
    rsys.addexport()
    # add import constraints
    # rsys.addimport()
    rsys.addimport_without([src])

    # the selected AS can select best route flexibly, but follow the bgp protocol and select a received route..
    rsys.addimport_bgp([src])

    #       done in rsys
    rsys.checkwaypoint(src, neighbor)

    rsys.solver.set("timeout", 600000)

    localtime = time.asctime(time.localtime(time.time()))
    print ("start to check", localtime)
    totalt1 = time.time()

    rst = rsys.solver.check()

    totalt2 = time.time()
    if opt:
        state["ITE_src_time_opt"] = totalt2 - totalt1
    else:
        state["ITE_src_time"] = totalt2 - totalt1

    localtime = time.asctime(time.localtime(time.time()))

    print ("********************************finish ITE_src", localtime, totalt2 - totalt1, rst)

    #    if rst == sat:
    #        printresult(rsys.solver)
    if opt:
        state["ITE_src_result_opt"] = rst
    else:
        state["ITE_src_result"] = rst

    return rsys


def check_ITE_n(opts, args, dest, neighbor, src, state, rsys = None, calprovider = False, opt = False, trim = True,
                violateexport = 0.0, violateimport = 0.0):
    tag = " "
    if opt:
        tag = "_opt "
    print("*******************************************start ITE_neighbor check", tag)
    localtime = time.asctime(time.localtime(time.time()))
    print "start initialize verifier", localtime
    #    sys.setrecursionlimit(65535)
    # initialize verifier. False means no special policy generation
    if rsys == None:
        rsys = Verifier(opts, args, flag = False, violateexport = violateexport, violateimport = violateimport)
        if calprovider:
            localtime = time.asctime(time.localtime(time.time()))
            print "compute provider cone start", localtime
            rsys.topo.computeprovidercone()
            localtime = time.asctime(time.localtime(time.time()))
            print "compute provider cone end", localtime
    else:
        rsys.clear()

    localtime = time.asctime(time.localtime(time.time()))
    print "finish initialize verifier", localtime

    rsys.setwaypoint(neighbor)

    # set up origin (should before import constraints)
    # when ORIGIN == ATTACKER, there is no attacker
    #    ORIGIN = 1
    #    ATTACKER = 1
    #    VICTIM = 25
    rsys.solver.add(rsys.topo.selectorigin(dest))

    time1 = time.time()
    localtime = time.asctime(time.localtime(time1))
    print "start topotrim", localtime
    # origin, victim, attacker
#    rsys.topo.topotrim(dest, src, dest, trim = trim)
    rsys.topo.topotrim_new([dest], [src], trim = trim)
    state["trim"] = True

    time2 = time.time()
    localtime = time.asctime(time.localtime(time2))
    print "finish topotrim", localtime
    state["trimtime"] = time2 - time1

    rsys.topo.trimstat()

    state["selected_node"] = rsys.topo.selectednodesnum
    state["selected_edge"] = rsys.topo.selectededgenum
    print("selected node:", state["selected_node"])
    print("selected edge:", state["selected_edge"])

    # generate necessary records after dag trim
    rsys.topo.gen_records()

    time1 = time.time()
    localtime = time.asctime(time.localtime(time1))
    print "finish record generation trim.", localtime


    # add export constraints
    rsys.addexport_without([dest])
    # add import constraints
    rsys.addimport()

    #       done in rsys
    rsys.checkwaypoint(src, neighbor)

    rsys.property_hasroute(src)

    rsys.setup_ITE_neighbor(dest, opt = opt, selected_neighbor = neighbor)

    # new change
    rsys.setupleaves()

#    rsys.solver.set("timeout", 1800000)

    time2 = time.time()
    localtime2 = time.asctime(time.localtime(time2))
    print ("start to check", localtime2)
    state["gen_time"] = time2 - time1
    totalt1 = time.time()

    rst = rsys.solver.check()

    totalt2 = time.time()
    if opt:
        state["ITE_neighbor_time_opt"] = totalt2 - totalt1
    else:
        state["ITE_neighbor_time"] = totalt2 - totalt1

    localtime = time.asctime(time.localtime(time.time()))

    print ("********************************finish ITE_neighbor", localtime, totalt2 - totalt1, rst)

#    if rst == sat:
#        printresult(rsys.solver)
    if opt:
        state["ITE_neighbor_result_opt"] = rst
    else:
        state["ITE_neighbor_result"] = rst


    return rsys


# optimization for ITE_neighbor
def ITE_neighbor_opt(opts, args):
    print("start verification for inbound traffic engineering (neighbor)")
    with open("./ITE_n_result.txt", "r") as f:
        states = pickle.load(f)
    print("ready for ITE_neighbor OPTIMIZATION:", states)
    rsys = None
    for state in states:
        print("----------------------opt for:", state)
        rsys = check_ITE_n(opts, args, state["dest"], state["selected_neighbor"], 15169, state, rsys = rsys, opt = True)
        if state["ITE_neighbor_result"] != state["ITE_neighbor_result_opt"]:
            print("result is different!!!!!!:", state["ITE_neighbor_result"], state["ITE_neighbor_result_opt"])
        if state["ITE_neighbor_time"] <= state["ITE_neighbor_time_opt"]:
            print("opt time is larger!!!!:", state["ITE_neighbor_time"], state["ITE_neighbor_time_opt"])
    print("optimization ITE_n result:", states)
    with open("./ITE_n_result_opt.txt", "w") as f:
        pickle.dump(states, f)


def ITE_src(opts, args):
    print("start verification for inbound traffic engineering (src)")
    with open("./ITE_n_candidate.txt", "r") as f:
        candidates = pickle.load(f)
    print(candidates)
    states = []
    rsys = None
    for k, v in candidates.iteritems():
        print("***********************************", str(len(states)), "*********************")
        state = {}
        state["dest"] = k
        state["neighbors"] = v
        state["src"] = 15169
        random.shuffle(v)
        state["selected_neighbor"] = v[0]
        rsys = check_ITE_src(opts, args, k, v[0], 15169, state, rsys = rsys)
        states.append(state)
    print("ITE_src result:", states)
    with open("./ITE_src_result.txt", "w") as f:
        pickle.dump(states, f)


def ITE_neighbor(opts, args, ifile = "./ITE_n_candidate.txt", ofile = "./ITE_n_result.txt", trim = True, violateexport = 0.0
                 , violateimport = 0.0):
    print("start verification for inbound traffic engineering (neighbor)")
    with open(ifile, "r") as f:
        candidates = pickle.load(f)
    print(candidates)
    states = []
#    with open(ofile, "r") as f:
#        states = pickle.load(f)
    rsys = None
    counter = 0
    for k, v in candidates.iteritems():
        if counter >= 10 and trim:
            break
        state = {}
        state["dest"] = k
        state["neighbors"] = v
        state["src"] = 15169
        random.shuffle(v)
        state["selected_neighbor"] = v[0]
        rsys = check_ITE_n(opts, args, k, v[0], 15169, state, rsys = rsys, trim = trim, opt = False, violateexport = violateexport,
                           violateimport = violateimport)
        states.append(state)
        counter += 1
    print("ITE_n result:", states)
    with open(ofile, "w") as f:
        pickle.dump(states, f)



def allinone(opts, args):
    print("start allinone method!")
    f = open("./stats.txt", "rb")
    stats = pickle.load(f)
    f.close()
    rsys = None
    newstats = []
    counter = 0
    totalcounter = 0
    for stat in stats:
#        if "result" in stat.keys() and stat["a"] in [136710, 201314, 266150, 59375, 395165]:
        if "announcement_num" in stat.keys() and stat["announcement_num"] >= 1:
            print ("try ", stat, "*************************************************", counter, "/", totalcounter)
            newstat = copy.copy(stat)
            rsys = veri_trafficattraction_allinone(opts, args, stat["o"], stat["v"], stat["a"], newstat, rsys = rsys)
            if len(newstat) > 0:
                newstats.append(newstat)
            else:
                print "-------------------------------------there are errors----------------------"

            if "result" in newstat.keys() and newstat["result"] != newstat["resultallinone"]:
                print "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!result and resultonepertime are not equal!!!!!!!!!!!!!!!!!!!!"
                print newstat
            print ("end ****************************************************************")
            print (newstat)
            counter += 1
        totalcounter += 1
    nf = open("newstats(allinone).txt", "wb")
    pickle.dump(newstats, nf)
    nf.close()


def testbestroute():
    optlist = []
    '''
    optlist.append([("-r", "../topos/small550.txt")])
    optlist.append([("-r", "../topos/small600.txt")])
    optlist.append([("-r", "../topos/small650.txt")])
    optlist.append([("-r", "../topos/small700.txt")])
    optlist.append([("-r", "../topos/small750.txt")])
    optlist.append([("-r", "../topos/small800.txt")])
    optlist.append([("-r", "../topos/small850.txt")])
    optlist.append([("-r", "../topos/small900.txt")])
    optlist.append([("-r", "../topos/small950.txt")])
    optlist.append([("-r", "../topos/small1000.txt")])
    '''

    optlist.append([("-r", "../topos/intratopo.txt")])
    counter = 0

    for opts in optlist:
        print("start:" + str(opts) + "--------------------------------------")
        gen_bestroute(opts, None, 1, 25, trim=False, num=counter)
        counter += 1



def multi_testibgp(trim = True):
    for i in range(100, 600, 100):
        opts = [("-r", "../topos/intratopo_" + str(i) + ".txt")]
        cands = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        rsys = Verifier(opts, None, flag = False)
        statelist = []
        if trim:
            ofilestr = "ibgp_stats_" + str(i) + "trim.txt"
        else:
            ofilestr = "ibgp_stats_" + str(i) + "notrim.txt"
        with open(ofilestr, "w") as ofile:
            for c in cands:
                print (c)
                #                statelist.append(veri_hijacking(opts, args, cands=c, verifier = rsys))
                statelist.append(testibgp(inORIGIN=c, opts = opts, trim = trim, violateimport = 0.3))
                rsys.clear()
            pickle.dump(statelist, ofile)
            print("finish" + str(opts) + "------------------------------")
            print(statelist)

def testibgp(inORIGIN = 1, inVICTIM = 25, trim = False, opts = [("-r", "../topos/intratopo.txt")], violateimport = 0.0):
    args = None
    states = {}
    states["origin"] = inORIGIN

    rsys = gen_rsys(opts, args, inORIGIN, inVICTIM, inORIGIN, trim=trim, alltrim = True, stat=states,
                    violateimport= violateimport)

    t1 = time.time()
    localtime = time.asctime(time.localtime(t1))
    print ("start generate constraints", localtime)
    # add export constraints
    rsys.addexport()
    # add import constraints
    rsys.addimport()

    rsys.property_allhasroute()

    # when it is not trimed, the leaves should be setup for valid#
#    rsys.setupleaves()

    t2 = time.time()
    localtime = time.asctime(time.localtime(t2))
    print ("finish generate constraints", localtime)
    states["gen_constraints"] = t2 - t1

    # add traffic attraction property
    #    rsys.addproperty(VICTIM, ATTACKER)

    t1 = time.time()
    localtime = time.asctime(time.localtime(t1))
    print "start checking", localtime
    rst = rsys.solver.check()
    t2 = time.time()
    localtime = time.asctime(time.localtime(t2))
    print "result:", rst, localtime
    print rsys.solver.statistics()
    states["result"] = rst
    states["checking_time"] = t2 - t1
    states["dotrim"] = trim

    states["asnum"] = len(rsys.topo.dict)
    states["linknum"] = rsys.topo.relationnum

    print(states)
    return states

#    with open("./ibgp_" + str(num) + ".txt", "w") as f:
#        pickle.dump(states, f)

    if rst == sat:
        #    printresult(rsys.solver)
        # return
        print(rst)
    elif rst == unsat:
        print(rst)


#        for c in rsys.solver.assertions():
#            print c


def main(argv = None):
    if argv is None:
        argv = sys.argv
    try:
        try:
            opts, args = getopt.getopt(argv[1:], "hr:", ["relationfile="])
        except getopt.error as msg:
            raise Usage(msg)
    except Usage as err:
        print>>sys.stderr, err.msg
        print >> sys.stderr, "for help use --help"
        return 2
    print(opts)
    print(args)


#    testbestroute()

#    testibgp(trim = True)
#    multi_testibgp(trim = True)

#    stat = {}
#    veri_trafficattraction(opts, args, 31744, 56794, 37643, stat)
#    print stat
    # way point when links might break: origin, source,
#    waypoint_link_break(opts, args, 1, 25, 174)
#    generatefaketopo(opts, args, -1)

    # the vanilla version of hijacking
    # generate stats.txt as the testing base
#    NUM = 100
#    multi_hijacking(opts, args, NUM)
    # test hijacking on multiple topos for paper
    multi_topo_hijacking(trim = False, smallscale = True, policyaware = True, violateexport = 0.0,
                         violateimport = 0.0)

    # only find plist once
    # announce all routes to neighbors, and emunerate all announcemenets that might help other announcements.
    #allinone(opts, args)




    # verification for inbound traffic engineering: prefer a specific neighbor.
    # announce different routes to different neighbors
#    cand4ITEN(opts, args)
#    ITE_neighbor(opts, args)
    #ITE_neighbor_opt(opts, args)

    # test ite on multiple topos for paper
#    multiple_ite(trim = False, smallscale = True, violateexport = 0.1, violateimport = 0.1)

    # verification for inbound traffic engineering: prefer a specific neighbor.
    # the src AS, google, use different import policy
#    ITE_src(opts, args)
#    ITE_src_opt(opts, args)


if __name__ == '__main__':
    sys.exit(main())