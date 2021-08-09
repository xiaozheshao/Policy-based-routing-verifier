import codecs
import time
import random

from node import *
#from asqueue import *
from random import choice

class Topo:
    def __init__(self, file_name, fakenum = 0, violateexport = 0.0, violateimport = 0.0):
        self.violateexport = violateexport
        self.violateimport = violateimport
        # number of ASs after trim
        self.ASNUM = 0
        # number of all ASs
        self.ASNUMTotal = 0
        # dictionary to store all nodes (ASid, node)
        self.dict = {}

        # a dictionary to index all ASs (provider index, AS)
        self.providerindex2as = {}

        self.relationnum = 0


        # read AS relationship from input file
        self.read_relation(file_name)
        # generate DAG
#        self.gen_dag()
        # generate edge records
#        self.gen_records()

        # generate the export policy for each AS
        self.genpolicy()



        self.allkeys = list(self.dict.keys())
        random.shuffle(self.allkeys)
        self.printstat()
        self.cycles = []
        self.hascycle = False

        self.selectededgenum = 0
        self.selectednodesnum = 0

        # store the fake node instead of the id
        self.fakenodes = set()
        self.tier1 = set()

        if fakenum > 0:
#        self.genfakenodes(self.ASNUMTotal)
            self.genfakenodes(fakenum)
            self.outputfaketopo()

        # actually is the provider neighbor
        self.att_neighbors = set()
        self.att_allneighbors = set()
        self.att_neighbor_num = 0


    def clear(self):
        # trim will redo
        self.ASNUM = 0
        for id, net in self.dict.iteritems():
            # clear each AS
            net.clear()
        self.selectededgenum = 0
        self.selectednodesnum = 0
        self.att_neighbors = set()
        self.att_allneighbors = set()
        self.att_neighbor_num = 0

####################################################################################### for fake nodes


    def outputfaketopo(self):
        print("start output fake topo.")
        with open("../topos/faketopo.txt", "w") as file:
            rst = self.outputclique()
            file.write(rst)
            self.outputfakenodeid(file)
            rst = self.outputlinks(file)
        print("end output fake topo.")


    def outputfakenodeid(self, file):
        for id in self.fakenodes:
            file.write("# fake node:" + str(id.asid) + "\n")

    def outputclique(self):
        out = "# clique: "
        for id, asnode in self.dict.iteritems():
            if len(asnode.providers) < 1:
                out += " " + str(id)
        out += "\n"
        return out

    def outputlinks(self, file):
        for id, asnode in self.dict.iteritems():
            for c in asnode.customers:
                file.write(str(id) + "|" + str(c) + "|-1\n")
            for p in asnode.peers:
                if p < asnode.asid:
                    file.write(str(id) + "|" + str(p) + "|0\n")


    def computeprovidercone(self):
        counter = 0
        for id, asnode in self.dict.iteritems():
            asnode.providerindex = counter
            counter += 1
            self.providerindex2as[counter] = asnode
        for id, asnode in self.dict.iteritems():
            asnode.calprovidercone()

    def computecustomercone(self):
        for id, asnode in self.dict.iteritems():
            asnode.calcustomercone()


    # generate fake nodes: num is the number of fake nodes
    def genfakenodes(self, num):
        if num == -1:
            num = self.ASNUMTotal
        print ("start generate ", num, " fake nodes")
        self.computecustomercone()
        startid = 0
        for i in range(0,num):
            print("generate fake node:", i)
            startid = self.gensinglefake(i, startid)
        print ("finish fake node generation")


    def selectasnumber(self, lastid):
        for i in range(lastid + 1, 99999999):
            if i not in self.dict.keys():
                return i
        print("No spare as number!!!")
        return 0

    def avgdegree(self):
        degree = 0
        for id, asnode in self.dict.iteritems():
            degree += len(asnode.neighbors)
        return degree

    # generate a single fake node
    def gensinglefake(self, index, lastid):
        id = self.selectasnumber(lastid)
        self.ASNUMTotal += 1
        fakenode = AS(id, self.ASNUMTotal, self.dict)
        avgdegree = self.avgdegree()
        avgdegree = avgdegree / self.ASNUMTotal / 2
        self.fakenodes.add(fakenode)
        self.addcustomers(fakenode, avgdegree)
        self.addproviders(fakenode, avgdegree)
        self.addpeers(fakenode, avgdegree)
#        self.tier1check(fakenode, avgdegree)
        self.dict[id] = fakenode
        return id

    def updatetier1(self):
        self.tier1 = set()
        for id, asnode in self.dict.iteritems():
            if len(asnode.providers) < 1:
                self.tier1.add(id)

    def tier1check(self, fakenode, avgdegree):
        if len(fakenode.providers) < 1:
            # add as tier1
            self.updatetier1()
            for id in self.tier1:
                if id not in fakenode.peers:
                    if id in fakenode.neighbors:
                        print("Error!!!!", id, " is already a neighbor of AS ", fakenode.asid)
                        continue
                    fakenode.addrel(id, 2)
                    self.dict[id].addrel(fakenode.asid, 2)


    # add customers for fake nodes
    def addcustomers(self, node, degree):
        totalproviders = 0
        for id, asnode in self.dict.iteritems():
            totalproviders += len(asnode.providers)
        for id, asnode in self.dict.iteritems():
            pnum = len(asnode.providers)
            r = random.random()
            if r <= 1.0 * pnum / totalproviders:
                asnode.addrel(node.asid, 1)
                node.addrel(asnode.asid, 0)
#                node.customercone.update(asnode.customercone)
                node.customercone = node.customercone | asnode.customercone


    def incustomercone(self, p, c):
        return p.customercone[c]


    # c can be the customer of p
    def canbecustomer(self, p, c):
        for cc in c.getcustomers():
#            if cc not in self.fakenodes:
#                flag = self.iscustomers(p.asid, cc)
                flag = self.incustomercone(p, cc)
                if flag:
                    continue
                else:
                    return False
        return True

    # add providers for fake nodes
    def addproviders(self, node, degree):
        sumcustomers = 0
        potentialprovider = set()
        for id in set(self.dict.keys()) - node.neighbors:
            flag = self.canbecustomer(self.dict[id], node)
            if flag:
                potentialprovider.add(id)
                sumcustomers += len(self.dict[id].getcustomers())
        for id in potentialprovider:
            asnode = self.dict[id]
            cnum = len(asnode.getcustomers())
            r = random.random()
            if r <= 1.0 * cnum / sumcustomers:
                asnode.addrel(node.asid, 0)
                node.addrel(asnode.asid, 1)
                asnode.customercone = asnode.customercone | node.customercone
#                asnode.customercone.update(node.customercone)

    def addpeers(self, node, degree):
        sumpeers = 0
        potentialpeers = set()
        for id in set(self.dict.keys()) - node.neighbors:
            potentialpeers.add(id)
            sumpeers += len(self.dict[id].getpeers())
        for id in potentialpeers:
            asnode = self.dict[id]
            pnum = len(asnode.getpeers())
            r = random.random()
            if r <= 1.0 * pnum / sumpeers:
                asnode.addrel(node.asid, 2)
                node.addrel(asnode.asid, 2)

#################################################################### for fake nodes end

    def selected(self, asid):
        node = self.dict[asid]
        return node.dnode.selected or node.unode.selected


    def topoprint(self):
        # print the trimed topology for debugging
        for id, asnode in self.dict.iteritems():
            if asnode.dnode.selected:
                asnode.dnode.upstreamprint()
            if asnode.unode.selected:
                asnode.unode.upstreamprint()

    def rankingprint(self):
        # print raning of nodes
        for id, asnode in self.dict.iteritems():
            asnode.printout()
            asnode.dnode.printout()
            asnode.unode.printout()

    # after trim, print selected neighbors of the given target
    def neighborstat(self, target):
        dindrst = set()
        uindrst = set()
        dinurst = set()
        uinurst = set()
        counter = 0
        targetnet = self.dict[target]
        for id, asnode in self.dict.iteritems():
            if asnode.dnode.selected:
                if target in asnode.neighbors:
                    if targetnet.dnode in asnode.dnode.downnodes:
                        counter += 1
                        dindrst.add(id)
                    if targetnet.unode in asnode.dnode.downnodes:
                        counter += 1
                        uindrst.add(id)
            if asnode.unode.selected:
                if target in asnode.neighbors:
                    if targetnet.unode in asnode.unode.downnodes:
                        counter += 1
                        uinurst.add(id)
                    if targetnet.dnode in asnode.unode.downnodes:
                        counter += 1
                        dinurst.add(id)

        print ("target ", target, " has ", counter, " neighbors (dnodes and unodes). only for announcements")
        print ("downnode has downnode neighbors:", dindrst)
        print ("upnode has downnode neighbors:", uindrst)
        print ("downnode has upnode neighbors:", dinurst)
        print ("upnode has upnode neighbors:", uinurst)
        self.att_neighbors = dindrst
        self.att_allneighbors = dindrst | uindrst | dinurst | uinurst
        self.att_neighbor_num = counter
        return counter

    def trimstat(self):
#        self.rankingprint()
#        self.topoprint()
        print "Number of selected nodes:", self.selectednodesnum, " account to", \
            self.selectednodesnum / 2.0 / (self.ASNUMTotal - 1)
        edgenum = 0

        for id, asnode in self.dict.iteritems():
            if asnode.dnode.selected:
                for node in asnode.dnode.upnodes:
                    if node.selected:
                        edgenum += 1
            if asnode.unode.selected:
                for node in asnode.unode.upnodes:
                    if node.selected:
                        edgenum += 1
        self.selectededgenum = edgenum
        print edgenum, " edges are selected"
        rr = 0
        if self.selectednodesnum + self.selectededgenum > 0:
            rr = 2.0 * (self.ASNUMTotal - 1 + self.relationnum)/ (self.selectededgenum + self.selectednodesnum)
            print("rr:", rr)
        return rr

    # setup the origin route
    def selectorigin(self, origin):
        node = self.dict[origin]
        return node.setuporigin()

    def selectattacker(self, attacker):
        node = self.dict[attacker]
        node.isattacker = True
#        return node.setupattacker(self.ASNUM)

    # generate announcemenet graph
    def buildgraph(self):
        for id, network in self.dict.iteritems():
            network.buildconnection_all()


    # generate PeerBoost policies in the AS topology
    def gen_PB(self, flag = True):
        for id, network in self.dict.iteritems():
            # generate special peers for each AS
            network.gen_peers(flag)

    # setupleaves: make leaves dbest as valid
    def setupleaves(self):
        list = []
        for asid, node in self.dict.iteritems():
            list.append(node.setupleaves())
        return list

    # genereate all records
    def gen_records(self):
        for id, node in self.dict.iteritems():
            node.record_init(self)


    # generate dag (for Gao-Rexford guidelines)
#    def gen_dag(self):
#        for id, node in self.dict.iteritems():
#            node.dlinks |= node.customers
#            node.ulinks |= node.providers | node.peers


    def read_relation(self, file_name):
        # read AS relationship from CAIDA file
        text_file = open(file_name, "r")
        print("open AS relation file:", file_name)
        for line in text_file:
            if not line.startswith("#"):
                read_line = line.strip('\n').split('|')
                self.add_relation(read_line)

        #increase ASNUM by one for aspath encoding !!!
        self.ASNUMTotal += 1

        text_file.close()
        print(self.relationnum, "AS relations.")
        self.findcycle()
        print "finish cycle check!"


    def add_relation(self, line):
        # add one AS connection
        # print(line)
        self.relationnum = self.relationnum + 1
        read_line = []
        for i in line:
            read_line.append(int(i))
        # print(read_line)
        if read_line[2] == -1:
            rel1 = 0  # proider - customer
            rel2 = 1  # customer - provider
        elif read_line[2] == 0:
            rel1 = 2  # peer-peer
            rel2 = 2

        # add AS 1
        if self.dict.__contains__(read_line[0]):
            self.dict.get(read_line[0]).addrel(read_line[1], rel1)
        else:
            self.ASNUMTotal += 1
            node = AS(read_line[0], self.ASNUMTotal, self.dict, extra_export = self.violateexport,
                      prefer_rate = self.violateimport)
            node.addrel(read_line[1], rel1)
            self.dict[read_line[0]] = node

        # add AS 2
        if self.dict.__contains__(read_line[1]):
            self.dict.get(read_line[1]).addrel(read_line[0], rel2)
        else:
            self.ASNUMTotal += 1
            node = AS(read_line[1], self.ASNUMTotal, self.dict, extra_export = self.violateexport,
                      prefer_rate = self.violateimport)
            node.addrel(read_line[0], rel2)
            self.dict[read_line[1]] = node


    def printstat(self):
        isolatednum = 0
        linknum = 0
        peerlinknum = 0
        pepespecial = 0
        peprspecial = 0
        prpespecial = 0
        for n, value in self.dict.items():
            nnet = self.idtonet(n)
            if nnet.isisolated():
                isolatednum = isolatednum + 1
            linknum = linknum + len(nnet.getneighbors())
            penumber = len(nnet.getpeers())
            peerlinknum = peerlinknum + penumber
            prnumber = len(nnet.getproviders())
            pepespecial = pepespecial + 2 * penumber * (penumber - 1)
            peprspecial = peprspecial + penumber * prnumber
            prpespecial = prpespecial + prnumber * penumber
        print("peer to peer special arrangements:" + str(pepespecial))
        print("peer to provider special arrangement:" + str(peprspecial))
        print("provider to peeer special arrangement:" + str(prpespecial))
        print("Total special arrangement:" + str(pepespecial + peprspecial + prpespecial))
        print("isolated AS number:" + str(isolatednum))
        print("number of links:" + str(linknum/2))
        print("number of peer links:" + str(peerlinknum/2))
        print("number of ASs:" + str(len(self.dict.keys())))
#        print("Number of extra route:" + str(self.extraroutenum))


    def idtonet(self, asid):
        return self.dict[asid]


    def findcycle(self):
        visitedas = set()
        asqueue = []
        for asid, node in self.dict.iteritems():
            self.traversal(asid, visitedas, asqueue)



    def traversal(self, asid, visitedas, asqueue):
        if asid not in visitedas:
            if asid in asqueue:
                print "cycle:", asqueue
            else:
                asqueue.append(asid)
                asnet = self.dict[asid]
                for customer in asnet.customers:
                    self.traversal(customer, visitedas, asqueue)
                visitedas.add(asid)
                asqueue.pop()

    # describe whether customers is descendants.
    def iscustomers(self, provider, customer):
        if customer in self.dict[provider].customers:
            return True
        else:
            for cnet in self.dict[provider].customers:
                if self.iscustomers(cnet, customer):
                    return True
        return False


    # deep first search from point to node below lowbound
    # return True, if the node is selected
    def marktraverse(self, point):
        if point.visited:
            return point.selected
        else:
            point.visited = True
            flag = False
            for nextpoint in point.downnodes:
                if self.marktraverse(nextpoint):
                    flag = True
            point.selected = flag
            if flag:
                self.selectednodesnum += 1
            return point.selected
        return False


    # find nodees that are required. From src directed to dst
    def marknodes(self, src, dst, attacker):
        if not src.visited:
            if src == attacker:
                self.selectednodesnum += 1
            else:
                self.selectednodesnum += 2
        src.visited = True
        src.selected = True
        attacker.visited = True
        attacker.selected = True
#        lowbound = src.ranking if src.ranking < attacker.ranking else attacker.ranking
        self.marktraverse(dst)

    # after trim, reassign index to ASs whose dnode or unode is selected
    # called after trim and before constrant generation
    def reindex(self):
        for id, asnode in self.dict.iteritems():
            if asnode.dnode.selected or asnode.unode.selected:
                self.ASNUM += 1
                asnode.index = self.ASNUM
#                asnode.printout()
            else:
                asnode.index = -1
        self.ASNUM += 1


    # perform topo trim
    def topotrim(self, origin, victim, attacker, trim = True):
        if trim:
#            print "Origin node is", origin, "index", self.dict[origin].index, " Victim node is", victim, "index", \
#                self.dict[victim].index, " Attacker node is", attacker, "index", self.dict[attacker].index
            iscustomer = self.iscustomers(victim, origin)
            if iscustomer:
#                print ("origin ", origin, " is customer of victim ", victim)
                self.marknodes(self.dict[origin].dnode, self.dict[victim].dnode, self.dict[attacker].dnode)
                self.dict[victim].unode.visited = True
                self.dict[victim].unode.selected = True
            else:
#                print ("origin ", origin, " is not customer of victim ", victim)
                self.marknodes(self.dict[origin].dnode, self.dict[victim].unode, self.dict[attacker].dnode)
                self.dict[victim].unode.visited = True
                self.dict[victim].unode.selected = True
        else:
 #           print("do not trim the topology")
            # all nodes in the graph are selected
            for asid, node in self.dict.iteritems():
                node.dnode.selected = True
                node.unode.selected = True
        self.reindex()

    # directed graph traversal following the direction
    def traverse(self, point):
        if point.visited:
            return
        else:
            point.visited = True
            for nextpoint in point.upnodes:
                self.traverse(nextpoint)
            return

    # directed graph traversal following the reversed direction
    def retraverse(self, point):
        if point.revisited:
            return
        else:
            point.revisited = True
            for nextpoint in point.downnodes:
                self.retraverse(nextpoint)
            return

    def traverse_new(self, point, last):
        if point.visited:
            return
        pnet = point.asnode
        lnet = last.asnode
        # normal case
        if pnet.asid == lnet.asid or (lnet.asid in pnet.customers):
            point.visited = True
            for nextpoint in point.upnodes:
                self.traverse_new(nextpoint, point)
            return
        else:
            # special arrangement
            if last in point.halfvisited:
                # has visited point from last
                return
            point.halfvisited.add(last)
            for nextpoint in point.upnodes:
                id = nextpoint.asnode.asid
                if (id == pnet.asid) or id in pnet.customers:
                    self.traverse_new(nextpoint, point)
                elif lnet.asid in pnet.neighborreceive[id]:
                    self.traverse_new(nextpoint, point)



#    def retraverse_new(self, point, last):




    # new algorithm in the paper. work for cycle
    def topotrim_new(self, originlist, targetlist, trim = True, policyaware = True):
        if trim:
            for o in originlist:
                onet = self.dict[o]
                if policyaware:
                    self.traverse_new(onet.dnode, onet.dnode)
                else:
                    self.traverse(onet.dnode)
            for t in targetlist:
                tnet = self.dict[t]
                if policyaware:
#                    self.retraverse_new(tnet.unode, tnet.unode)
                    self.retraverse(tnet.unode)
                else:
                    self.retraverse(tnet.unode)
            for id, net in self.dict.iteritems():
                dnode = net.dnode
                unode = net.unode
                if (dnode.visited or len(dnode.halfvisited)>0 ) and dnode.revisited:
                    dnode.selected = True
                    self.selectednodesnum += 1
                if (unode.visited or len(unode.halfvisited)>0 )  and unode.revisited:
                    unode.selected = True
                    self.selectednodesnum += 1
        else:
            # print("do not trim the topology")
            # all nodes in the graph are selected
            for asid, node in self.dict.iteritems():
                node.dnode.selected = True
                node.unode.selected = True
        self.reindex()


    # generate policy for each AS
    def genpolicy(self):
        for id, net in self.dict.iteritems():
            net.initexportrule()

    # generate policy for each AS
#    def genpolicy(self):
#        for id, net in self.dict.iteritems():
#            net.initexportrule()

    def addclient(self, rrset):
        degree = 0
        for id in rrset:
            net = self.dict[id]
            degree += len(net.neighbors)
        newid = self.ASNUMTotal + 1
        for i in rrset:
            r = random.random()
            rate = len(self.dict[i].neighbors) * 1.0 / degree
            if r < rate:
                self.add_relation([i, newid, -1])


    # generate intra topology: router reflector and clients
    def gen_intratopo(self, rrnum = 10, clientnum = 100, ofile = "../topos/intratopo.txt"):
        for i in range(1, rrnum + 1):
            for j in range(1, i):
                self.add_relation([i,j, 0])
#        self.ASNUMTotal = len(self.dict)
        rrset = self.dict.keys()
        for i in range(0, clientnum):
            self.addclient(rrset)


        while (True):
            connectedset = []
            # guarnatee all nodes are connected
            for id, net in self.dict.iteritems():
                if len(net.neighbors) > 0:
                    connectedset.append(id)
            if len(connectedset) >= rrnum + clientnum:
                break
            for i in range(0, rrnum + clientnum - len(connectedset) ):
                self.addclient(rrset)


        with open(ofile, "w") as outfile:
            self.outputtopo(connectedset, outfile)



    # generate a smaller topo with num nodes and store it into file
    # always contain AS src
    def gen_smalltopo(self, file, num, src):
        selected = set()
        selected.add(src)
        last = src
        while len(selected) < num:
            last = self.selectone(last)
            selected.add(last)
        print ("select ", num, " ASs.")
        with open(file, "w") as f:
            f.write("#There are " + str(num) + " ASs.\n")
            self.outputtopo(selected, f)

    def outputtopo(self, selected, f):
        for n in selected:
            nnet = self.dict[n]
            for p in nnet.peers:
                if p < n and p in selected:
                    f.write(str(n) + "|" + str(p) + "|0\n")
            for c in nnet.customers:
                if c in selected:
                    f.write(str(n) + "|" + str(c) + "|-1\n")

    def selectone(self, src):
        srcnet = self.dict[src]
        return choice(list(srcnet.neighbors))

