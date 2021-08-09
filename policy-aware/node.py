from z3 import *
import random
from BitVector import *

class Node:

    def __init__(self, asnode, isdownnode):


        # DAG might have cycle in PeerBoost

        self.asnode = asnode
        self.isdownnode = isdownnode


        # how many incoming edge are left. used for topological sorting
        self.inedge = 0

        # topological ranking
#        self.ranking = 0

        # used in marking nodes
        self.visited = False
        # whether the node is selected in the final DAG
        self.selected = False
        # used in the reversed traversal
        self.revisited = False

        # record the inbound node
        self.halfvisited = set()

#        self.dstreamnodes = None

        # downstream nodes in DAG
        # routes come from downnodes
        # income node
        self.downnodes = set()


        # upstream nodes in DAG
        # outgoing node
        self.upnodes = set()

    # clear the visited flags for each AS.
    # do not change the transformed graph
    def clear(self):
        self.inedge = 0
#        self.ranking = 0
        self.visited = False
        self.selected = False
        self.revisited = False

        self.halfvisited = set()


    def idprint(self):
        print "AS", self.asnode.asid, "down node?", self.isdownnode

    def upstreamprint(self):
        print "Node:", self.asnode.asid, "down node?:", self.isdownnode, "Upstream node list:"
        for node in self.upnodes:
            if node.selected:
                node.idprint()

    def adddstream(self, node):
        self.downnodes.add(node)


    def addustream(self, node):
        self.upnodes.add(node)


    def printout(self):
        print "Node ranking:", '''self.ranking,''' "visited?", self.visited, "revisited?", self.revisited, "selected?", self.selected, "inedge:", self.inedge

class Record:
    def __init__(self, name):
        # TODO
        self.name = name
        # treat aspath as nexthop
        self.aspath = Int('%sa' % self.name)
#        self.nexthop = Int('%sn' % self.name)
        # how many hops
        self.length = Int('%sl' % self.name)
        # whether it is a valid route
        self.valid = Bool('%sv' % self.name)
        # whether it is a downhill route
#        self.droute = Bool('%sd' % self.name)
        # backup level
#        self.backup = Int('%sb' % self.name)
        # new variable for waypoint: whether the record go through a specific AS
        self.flag = Bool('%sf' % self.name)
        # local preference
        self.loc = Int('%sp' % self.name)


class AS:
    # prefer_rate is the percentage that the AS violate GR preference rule
    def __init__(self, asid, index, asdict, origin = False, p2r = 0, r2p = 0, r2r = 0, prefp = 0,
                 prefer_rate = 0, extra_export = 0):
        self.p2r = p2r
        self.r2r = r2r
        self.r2p = r2p
        self.prefp = prefp

        self.prefer_rate = prefer_rate
        r = random.random()
        if r < self.prefer_rate:
            self.violateprefer = True
        else:
            self.violateprefer = False
        # whether already select a special neighbor to assign preferred local preference.
        self.violatepreferdone = False

        self.extra_export = extra_export
        r = random.random()
        if r < self.extra_export:
            self.violateexport = True
        else:
            self.violateexport = False
        self.violateexportdone = False



        # AS number
        self.asid = asid
        # index for the record variable
        self.index = index
        self.neighbors = set()
        self.customers = set()
        self.providers = set()
        self.peers = set()

        # preference of neighbors: (neighbor, locpref)
        # this field will be initialized in the func addrel


        # this loc value just used to
        self.neighborloc = {}

        # whether routes from src can be announced to dest; (dst, set(src))
        # dst only be peer and provider. customers receive all possible routes
        # provider routes should not be announced to provider
        self.neighborreceive = {}


        # for PeerBoost policy: type 1,2,3,4: OC peer, DH peer, common peer and UT peer
        self.DHpeers = set() # downhill peers, Not include OC peers.
        self.OCpeers = set() # over-customer peers.
        # treat routes from DH peers and OC peers as downhill peer routes.
        # other peer routes are uphill routes

        self.UHpeers = set() # common peers without special export and import policy. Namely, uphill peers
        self.UTpeers = set() # Upward transit peer selectively announces its uphill routes. The routes from UT peers are treated as uphill routes.

        # record special announcement, {id, set()}, {to, {from}}
        # downhill routes to peers. The step one is a subset of DtoPeer
        self.DtoPeer = {}
        self.DtoPeer_step = {}
        # uphill routes to peers
        self.UtoPeer = {}
        self.UtoPeer_step = {}
        # downhill routes to providers
        self.DtoProvider = {}
        self.DtoProvider_step = {}


        # DAG topology
#        self.dlinks = set()
#        self.ulinks = set()

        # Records to providers and customers
        self.records = {}
        # records to peers
        # for downhill peer routes. from the downside node to
        self.downpeerrecords = {}
        # for uphill peer routes. fro mthe upside node to
#        self.uppeerrecords = {}
        # change for journal version
        self.uppeerrecords = self.downpeerrecords


        self.dbest = Record('db_%s' % self.asid)
        self.best = Record('b_%s' % self.asid)

        self.origin = origin
        self.isattacker = False

        # downnode in DAG
        self.dnode = Node(self, True)
        # upnode in DAG
        self.unode = Node(self, False)

        self.dict = asdict

        # customer cone for generating fake nodes
        self.customercone = BitVector(size = 400000)
        self.customercone[self.asid] = 1
        self.customerconeflag = False

        self.providercone = BitVector(size = 70000)
        self.providerconeflag = False
        # used for the index in provider cone
        self.providerindex = -1

        self.iswaypoint = False




    def clear(self):
        # might have problem
        self.index = -1
        self.records.clear()
        self.downpeerrecords.clear()
        self.uppeerrecords.clear()
        self.origin = False
        self.isattacker = False
        self.dnode.clear()
        self.unode.clear()
        self.iswaypoint = False


    def calprovidercone(self):
        if self.providerconeflag == False:
            for node in self.providers:
                # first add all direct providers
                self.providercone[self.dict[node].providerindex] = 1
                if self.dict[node].providerconeflag:
                    self.providercone = self.providercone | self.dict[node].providercone
                else:
                    self.dict[node].calprovidercone()
                    self.providercone = self.providercone | self.dict[node].providercone
            self.providerconeflag = True



    def calcustomercone(self):
        if self.customerconeflag == False:
            for node in self.customers:
                if self.dict[node].customerconeflag:
                    self.customercone = self.customercone | self.dict[node].customercone
#                    self.customercone.update(self.dict[node].customercone)
                else:
                    self.dict[node].calcustomercone()
                    self.customercone = self.customercone | self.dict[node].customercone
#                    self.customercone.update(self.dict[node].customercone)
            self.customerconeflag = True
        return


    def printout(self):
        print "Node: id,", self.asid, "index,", self.index


    # build the connection between nodes in the graph
    # old version for PeerBoost
    def buildconnection(self):
        # for downnode
        for c in self.customers|self.OCpeers|self.DHpeers:
            # all customers, OC peers and DH peers
            cdnode = self.dict[c].dnode
            self.dnode.adddstream(cdnode)
            cdnode.addustream(self.dnode)

        # for upnode
        for peer in self.UTpeers|self.providers:
            # All UT peers and providers
            pnode = self.dict[peer].unode
            self.unode.adddstream(pnode)
            pnode.addustream(self.unode)

        for peer in self.UHpeers:
            # All UH peers. from dnode to unode
            pnode = self.dict[peer].dnode
            self.unode.adddstream(pnode)
            pnode.addustream(self.unode)

        self.unode.adddstream(self.dnode)
        self.dnode.addustream(self.unode)

    # connect to dst node, whether from downnode or upnode
    # return True for downnode
    # dst is asid
    def fromdnode(self, dst):
        srcset = self.neighborreceive[dst]
        for src in srcset:
            pref = self.neighborloc[src]
            if pref >= 7:
                continue
            else:
                return False
        return True

    # build the connection for all possible policies
    def buildconnection_all(self):
        for c in self.customers:
            # all customers, OC peers and DH peers
            if self.dict[c].fromdnode(self.asid):
                cdnode = self.dict[c].dnode
            else:
                cdnode = self.dict[c].unode
            self.dnode.adddstream(cdnode)
            cdnode.addustream(self.dnode)

        for p in self.providers:
            pnode = self.dict[p].unode
            pref = self.neighborloc[p]
            if pref >= 7:
                node = self.dnode
            else:
                node = self.unode
            node.adddstream(pnode)
            pnode.addustream(node)

        for peer in self.UHpeers:
            if self.dict[peer].fromdnode(self.asid):
                pnode = self.dict[peer].dnode
            else:
                pnode = self.dict[peer].unode
            pref = self.neighborloc[peer]
            if pref >= 7:
                node = self.dnode
            else:
                node = self.unode
            node.adddstream(pnode)
            pnode.addustream(node)


        self.unode.adddstream(self.dnode)
        self.dnode.addustream(self.unode)



    def gen_peers(self, flag=True):
        # flag is true: generate PB policy
        low = 1
        if not flag:
            low = 3
        if not flag:
            self.UHpeers.update(self.peers)
        else:
            for peer in self.peers:
                # for each peer, seperate OC, DH and UH
                r = random.randint(low,4)
                if r == 1:
                    self.OCpeers.add(peer)
                    print "AS", peer, " is OC peer of AS", self.asid
                elif r == 2:
                    self.DHpeers.add(peer)
                    print "AS", peer, " is DH peer of AS", self.asid
                else:
                    self.UHpeers.add(peer)
    #                print "AS", peer, " is UH peer of AS", self.asid


        # special routes to peers
        for peer in self.peers:
            downset = set()
            bdownset = set()
            upset = set()
            bupset = set()
            if flag:
                for peer2 in self.peers:
                    if peer != peer2:
                        rdown = random.randint(low, 10)
                        rup = random.randint(low, 10)
                        if rdown == 1:
                            downset.add(peer2)
                        if rdown == 2:
                            downset.add(peer2)
                            bdownset.add(peer2)
                        if rup == 1:
                            upset.add(peer2)
                        if rup == 2:
                            upset.add(peer2)
                            bupset.add(peer2)
                for provider in self.providers:
                    r = random.randint(low,10)
                    if r == 1:
                        upset.add(provider)
                    if r == 2:
                        upset.add(provider)
                        bupset.add(provider)
            self.DtoPeer[peer] = downset
            self.UtoPeer[peer] = upset
            self.DtoPeer_step[peer] = bdownset
            self.UtoPeer_step[peer] = bupset
            # when uphill routes are exported to another peer, when a uphill peer is exported to another peer,
            # the uphill peer is UT Peer
            self.UTpeers.update(upset - self.providers)


        # special routes to providers. only downhill routes can be exported
        for provider in self.providers:
            downset = set()
            bdownset = set()
            if flag:
                for peer in self.peers:
                    r = random.randint(low,10)
                    if r == 1:
                        downset.add(peer)
                    if r == 2:
                        downset.add(peer)
                        bdownset.add(peer)
            self.DtoProvider[provider] = downset
            self.DtoProvider_step[provider] = bdownset




    # an original route: a
    def origininit(self, a):
        return And(a.aspath == 0, a.length == 0, a.valid == True, a.backup == 0, a.droute == True)


    # set up origin route
    def setuporigin(self):
        self.origin = True
        return And(self.originroute(self.best), self.originroute(self.dbest))
#        return And(self.origininit(self.best), self.origininit(self.dbest))


    # set up leaf node that does not have customers
    def setupleaves(self):
        if not self.origin:
            # not origin and not a provider, downside route should be empty
#            if len(self.customers|self.OCpeers|self.DHpeers) < 1:
            validlist = []
            for n in self.dnode.downnodes:
                if n.selected:
                    validlist.append(n)
                    break
            if self.dnode.selected and len(validlist) == 0:
                return self.emptyinit(self.dbest)
        return True

#    def attackinit(self, a, ASNUM):
        #        return And(a.aspath % ASNUM == a.nexthop, a.aspath <= ASNUM ** a.length, a.length >= 0, a.aspath >= 0)
#        return And(a.aspath == 0, a.valid == True, a.nexthop == 0)

#    def setupattacker(self, ASNUM):
#        return And(self.attackinit(self.best, ASNUM), self.attackinit(self.dbest, ASNUM))

    def canexport_d(self, upnet, ASNUM):
        # return the condition that the dbest can be announced to upnet
        # TODO
        if self == upnet:
            # to the upnodes of the same AS
            rst = True
        else:
            if upnet.asid in self.providers:
                noexportable = (self.peers | self.providers) - self.neighborreceive[upnet.asid]
                #self.DHpeers - self.DtoProvider[upnet.asid]
            elif upnet.asid in self.peers:
                noexportable = (self.peers | self.providers) - self.neighborreceive[upnet.asid]
                #self.DHpeers - self.DtoPeer[upnet.asid]
            else:
                print "Error upnet!!!", upnet.id

            # check whether the dnode receive the routes from pnet
            tmp = set()
            for p in noexportable:
                pnet = self.dict[p]
                if pnet.dnode in self.dnode.downnodes or pnet.unode in self.dnode.downnodes:
                    tmp.add(p)

            noexportable = tmp


            if len(noexportable) > 0:
                # has no exportable neighbors
                orlist = [True]
                for neighbor in noexportable:
                    # change for journal version: an optimization
                    if (self.dict[neighbor].dnode.selected and self.dict[neighbor].dnode in self.dnode.downnodes) or \
                            (self.dict[neighbor].unode.selected and self.dict[neighbor].unode in self.dnode.downnodes):
                    #if self.dict[neighbor].dnode.selected or self.dict[neighbor].unode.selected:
                        # change for nexthop
                        orlist.append(Not(self.dbest.aspath == self.dict[neighbor].index))
                rst = And(orlist)
            else:
                rst = True
        return Or(And(self.dbest.valid, rst), self.isorigin(self.dbest))

    '''
    def canexport_d(self, upnet, ASNUM):
        # return the condition that the dbest can be announced to upnet
        # TODO
        if self == upnet:
            # to the upnodes of the same AS
            rst = True
        else:
            if upnet.asid in self.providers:
                # peer to provider
                exportable = self.customers | self.DtoProvider[upnet.asid]
            elif upnet.asid in self.peers:
                # peer to peer
                exportable = self.customers | self.DtoPeer[upnet.asid]
            else:
                print "Error upnet!!!", upnet.id
            if len(exportable) > 0:
                # has exportable neighbors
                orlist = []
                for neighbor in exportable:
                    if self.dict[neighbor].dnode.selected:
                        orlist.append(self.dbest.aspath % ASNUM == self.dict[neighbor].index)
                rst = Or(orlist)
            else:
                rst = False
        return Or(And(self.dbest.valid, rst), self.isorigin(self.dbest))
    '''

    def exportrecord_prepend(self, outr, ASNUM, upnode, isD, opt = False, selected = False):
        # generate the constraint when export the dbest to route outr
        # TODO
        length_incr = 32
        if selected:
            # when a neighbor is selected
            length_incr = 1
        if isD:
            # dbest to itself upnode
            if upnode.asnode == self:
                return True
            # for downside
            # regular constrain
            if self.iswaypoint:
                # change for nexthop
                if opt:
                    regular = And(outr.flag == True, outr.aspath == self.index,
                                  outr.length == self.dbest.length + length_incr, outr.valid == self.dbest.valid)
                else:
                    regular = And(outr.flag == True, outr.aspath == self.index, outr.length >= self.dbest.length + 1,
                              outr.length <= self.dbest.length + 32, outr.valid == self.dbest.valid)
            else:
                # change for nexthop
                if opt:
                    regular = And(outr.flag == self.dbest.flag, outr.aspath == self.index,
                              outr.length == self.dbest.length + length_incr, outr.valid == self.dbest.valid)
                else:
                    regular = And(outr.flag == self.dbest.flag, outr.aspath == self.index,
                              outr.length >= self.dbest.length + 1, outr.valid == self.dbest.valid,
                              outr.length <= self.dbest.length + 32)
            # consider backup level
#            if ((upnode in self.peers) and (upnode in self.DtoPeer_step)) or (
#                    (upnode in self.providers) and (upnode in self.DtoProvider_step)):
#                rst = And(outr.backup == self.dbest.backup + 1)
#            else:
#                rst = And(outr.backup == self.dbest.backup)
#            return And(regular, rst)
            return regular
        else:
            # for upwide
            if self.iswaypoint:
                # change for nexthop
                if opt:
                    regular = And(outr.flag == True, outr.aspath == self.index,
                                  outr.length == self.best.length + length_incr, outr.valid == self.best.valid)
                else:
                    regular = And(outr.flag == True, outr.aspath == self.index, outr.length >= self.best.length + 1,
                              outr.length <= self.dbest.length + 32,
                              outr.valid == self.best.valid)
            else:
                # change for nexthop
                if opt:
                    regular = And(outr.flag == self.best.flag, outr.aspath == self.index,
                              outr.length == self.best.length + length_incr, outr.valid == self.best.valid)
                else:
                    regular = And(outr.flag == self.best.flag, outr.aspath == self.index,
                              outr.length >= self.best.length + 1, outr.valid == self.best.valid,
                              outr.length <= self.dbest.length + 32)
            # consider backup level
#            if (upnode in self.peers) and (upnode in self.UtoPeer_step):
#                rst = And(outr.backup == self.best.backup + 1)
#            else:
#                rst = And(outr.backup == self.best.backup)
#            return And(regular, rst)
            return regular

    def exportrecord(self, outr, ASNUM, upnode, isD):
        # generate the constraint when export the dbest to route outr
        # TODO
        if isD:
            # dbest to itself upnode
            if upnode.asnode == self:
                return True
            # for downside
            # regular constrain
            if self.iswaypoint:
                # change for nexthop
                regular = And(outr.flag == True, outr.aspath == self.index, outr.length == self.dbest.length + 1,
                              outr.valid == self.dbest.valid)
            else:
                # change for nexthop
                regular = And(outr.flag == self.dbest.flag, outr.aspath == self.index,
                              outr.length == self.dbest.length + 1, outr.valid == self.dbest.valid)
            # consider backup level
#            if ((upnode in self.peers) and (upnode in self.DtoPeer_step)) or ((upnode in self.providers) and
            # (upnode in self.DtoProvider_step)):
#                rst = And(outr.backup == self.dbest.backup + 1)
#            else:
#                rst = And(outr.backup == self.dbest.backup)
            return And(regular)#, rst)
        else:
            # for upwide
            if self.iswaypoint:
                # change for nexthop
                regular = And(outr.flag == True, outr.aspath ==  self.index, outr.length == self.best.length + 1,
                              outr.valid == self.best.valid)
            else:
                # change for nexthop
                regular = And(outr.flag == self.best.flag, outr.aspath ==  self.index,
                              outr.length == self.best.length + 1, outr.valid == self.best.valid)
            # consider backup level
#            if (upnode in self.peers) and (upnode in self.UtoPeer_step):
#                rst = And(outr.backup == self.best.backup + 1)
#            else:
#                rst = And(outr.backup == self.best.backup)
            return And(regular)#, rst)

    # announce to pset and n. enumerate combination for pset and announce to n and no announce to others.
    def announceoriginroute_one(self, upnodes, records, ASNUM, pset, n):
        andlist = []
        for i in range(0, len(upnodes)):
            upnode = upnodes[i]
            record = records[i]
            if upnode.asnode.asid in pset:
                andlist.append(self.announceoriginroute(upnode, record, ASNUM))
            else:
                andlist.append(self.announceoriginroute2(upnode, record, ASNUM, n))
        return And(andlist)

    # announce to pset and n. enumerate combination for pset and announce to n and no announce to others.
    def announceoriginroute_allinone(self, upnodes, records, ASNUM, pset, qset):
        andlist = []
        for i in range(0, len(upnodes)):
            upnode = upnodes[i]
            record = records[i]
            if upnode.asnode.asid in pset:
                andlist.append(self.announceoriginroute(upnode, record, ASNUM))
            elif upnode.asnode.asid in qset:
                andlist.append(self.announceoriginroute2(upnode, record, ASNUM, upnode.asnode.asid))
        if len(qset) == 0:
            tmplist = []
            for i in range(0, len(upnodes)):
                tmplist.append(self.emptyinit_r(records[i]))
            if len(tmplist)>0:
                andlist.append(Not(And(tmplist)))
        return And(andlist)

    # announce to pset and qset
    def announceoriginroute_all(self, upnodes, records, ASNUM, pset, qset):
        andlist = []
        orlist = []
        for i in range(0, len(upnodes)):
            upnode = upnodes[i]
            record = records[i]
            if upnode.asnode.asid in pset:
                andlist.append(self.announceoriginroute(upnode, record, ASNUM))
            else:
                tmpandlist = []
                for j in range(0, len(upnodes)):
                    if upnodes[j].asnode.asid in qset:
                        tmpandlist.append(self.announceoriginroute2(upnodes[j], records[j], ASNUM, upnode.asnode.asid))
                if len(tmpandlist) > 0:
                    orlist.append(And(tmpandlist))
        if len(orlist) == 0 and len(andlist) == 0:
            return True
        elif len(orlist) == 0:
            return And(andlist)
        elif len(andlist) == 0:
            return Or(orlist)
        else:
            return And(And(andlist), Or(orlist))


    # announce to p and q
    def announceoriginroute3(self, upnode, record, ASNUM, p, q):
        if upnode.asnode.asid == p or upnode.asnode.asid == q:
            return And(record.flag == True, record.aspath == self.index, record.length == 1, record.valid == True, record.droute == upnode.isdownnode, record.backup == 0)
        else:
            return self.emptyinit(record)

    def announceoriginroute2(self, upnode, record, ASNUM, n):
        if upnode.asnode.asid == n:
            return And(record.flag == True, record.aspath == self.index, record.length == 1, record.valid == True, record.droute == upnode.isdownnode, record.backup == 0)
        else:
            return self.emptyinit(record)

    # announce any correct routes
    def announcecorrectroute(self, upnode, record, ASNUM):
            if self.iswaypoint:
                return Or(
                    And(record.flag == True, record.aspath == self.index, record.length >= 1, record.valid == True),
                    self.emptyinit_r(record))
            else:
                return Or(
                    And(record.flag == False, record.aspath == self.index, record.length >= 1, record.valid == True),
                    self.emptyinit_r(record))

    def announceoriginroute(self, upnode, record, ASNUM):
#        return And(record.flag == True, record.aspath == self.index, record.length == 1, record.valid == True, record.droute == upnode.isdownnode, record.backup == 0)
#        return And(self.emptyinit(record))
        # mimic the origin AS or do not announce any thing
        if self.iswaypoint:
#            if upnode.asnode.asid == 11164:
#                return And(record.flag == True, record.aspath == self.index, record.length == 1, record.valid == True, record.droute == upnode.isdownnode, record.backup == 0)
#            else:
#                return self.emptyinit(record)
            return Or(And(record.flag == True, record.aspath == self.index, record.length == 1, record.valid == True), self.emptyinit_r(record))
        else:
            return Or(And(record.flag == False, record.aspath == self.index, record.length == 1, record.valid == True), self.emptyinit_r(record))

#        return And(record.aspath == self.index, record.length == 1, record.valid == True, record.droute == upnode.isdownnode, record.backup == 0)
#        return And(self.emptyinit(record))

    def canexport_u(self, upnet, ASNUM):
        # return the condition that the best can be announced to record
        # TODO
        notexportable = set()
        if upnet.asid in self.peers | self.providers:
            # to peers
            notexportable = self.neighbors - self.customers - self.neighborreceive[upnet.asid] #- self.UtoPeer[upnet.asid]
        if len(notexportable) > 0:
            # routes from some neighbors can not be exported
            notlist = []
            for neighbor in notexportable:
                if neighbor in self.providers:
#                    if self.dict[neighbor].unode.selected:
                    #change for journal version: an optimization
                    if self.dict[neighbor].unode.selected and self.dict[neighbor].unode in self.unode.downnodes:
                        # change for nexthop
                        notlist.append(Not(self.best.aspath == self.dict[neighbor].index))
                if neighbor in self.peers:
#                    if self.dict[neighbor].dnode.selected or \
#                            (self.dict[neighbor].unode.selected and self.unode in self.dict[neighbor].unode.upnodes):
#change for journal version: an optimization
                    if (self.dict[neighbor].dnode.selected and self.dict[neighbor].dnode in self.unode.downnodes)or \
                            (self.dict[neighbor].unode.selected and self.unode in self.dict[neighbor].unode.upnodes):
                        # change for nexthop
                        notlist.append(Not(self.best.aspath == self.dict[neighbor].index))
            rst = And(notlist)
        else:
            rst = True
        return Or(And(self.best.valid, rst), self.isorigin(self.best))


    # def getrecord(self, upnode, flag):
    #     upnet = upnode.asnode
    #     if flag:
    #         # for downpeer
    #         if upnet.asid in self.peers:
    #             record = self.downpeerrecords[upnet.asid]
    #         else:
    #             record = self.records[upnet.asid]
    #     else:
    #         # for uppeer
    #         if upnet.asid in self.peers:
    #             record = self.uppeerrecords[upnet.asid]
    #         else:
    #             record = self.records[upnet.asid]
    #     return record


    # def attackstrategy_onepertime(self, dict, ASNUM, n, pset):
    #     records = []
    #     nodes = []
    #     if self.dnode.selected:
    #         # the downnode is selected
    #         for upnode in self.dnode.upnodes:
    #             if not upnode.selected:
    #                 continue
    #             if upnode.asnode == self:
    #                 # dbest announced to itself upnode
    #                 continue
    #             upnet = upnode.asnode
    #             if upnet.asid in self.peers:
    #                 record = self.downpeerrecords[upnet.asid]
    #             else:
    #                 record = self.records[upnet.asid]
    #             records.append(record)
    #             nodes.append(upnode)
    #     if self.unode.selected:
    #         # the upnode is selected
    #         for upnode in self.unode.upnodes:
    #             # for the upside of the DAG, export best
    #             if not upnode.selected:
    #                 continue
    #             upnet = upnode.asnode
    #             if upnet.asid in self.peers:
    #                 record = self.uppeerrecords[upnet.asid]
    #             else:
    #                 record = self.records[upnet.asid]
    #             records.append(record)
    #             nodes.append(upnode)
    #     return And(self.announceoriginroute_one(nodes, records, ASNUM, pset, n))


    def attackstrategy_allinone(self, dict, ASNUM, pset, qset):
        records = []
        nodes = []
        if self.dnode.selected:
            # the downnode is selected
            for upnode in self.dnode.upnodes:
                if not upnode.selected:
                    continue
                if upnode.asnode == self:
                    # dbest announced to itself upnode
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.downpeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                records.append(record)
                nodes.append(upnode)
        if self.unode.selected:
            # the upnode is selected
            for upnode in self.unode.upnodes:
                # for the upside of the DAG, export best
                if not upnode.selected:
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.uppeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                records.append(record)
                nodes.append(upnode)
        return And(self.announceoriginroute_allinone(nodes, records, ASNUM, pset, qset))



# 2 ^ provider with t * (customers + peers + provider without t)
    def attackstrategy_combine_opt(self, dict, ASNUM, pset, qset):
        records = []
        nodes = []
        if self.dnode.selected:
            # the downnode is selected
            for upnode in self.dnode.upnodes:
                if not upnode.selected:
                    continue
                if upnode.asnode == self:
                    # dbest announced to itself upnode
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.downpeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                records.append(record)
                nodes.append(upnode)
        if self.unode.selected:
            # the upnode is selected
            for upnode in self.unode.upnodes:
                # for the upside of the DAG, export best
                if not upnode.selected:
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.uppeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                records.append(record)
                nodes.append(upnode)
        return And(self.announceoriginroute_all(nodes, records, ASNUM, pset, qset))



# mauanlly select p and q to announce route.
    def attackstrategy_combine(self, dict, ASNUM, p, q):
        # return constraints from export policy
        ulist = [True]
        if self.dnode.selected:
            # the downnode is selected
            for upnode in self.dnode.upnodes:
                if not upnode.selected:
                    continue
                if upnode.asnode == self:
                    # dbest announced to itself upnode
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.downpeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                ulist.append(self.announceoriginroute3(upnode, record, ASNUM, p, q))


        dlist = [True]
        if self.unode.selected:
            # the upnode is selected
            for upnode in self.unode.upnodes:
                # for the upside of the DAG, export best
                if not upnode.selected:
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.uppeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
#                print("!!!!!!!!!!!!!!!!upnodes of attacker:", self.asid, " announce routes to ", upnet.asid)
                dlist.append(self.announceoriginroute3(upnode, record, ASNUM, p, q))

        if self.dnode.selected or self.unode.selected:
            return simplify(And(And(ulist), And(dlist)))
        else:
            return True


# assume that attacker send route to one neighbor a time. n is the selected neighbor to announcement
    def attackstrategy(self, dict, ASNUM, n):
        # return constraints from export policy
        ulist = [True]
        if self.dnode.selected:
            # the downnode is selected
            for upnode in self.dnode.upnodes:
                if not upnode.selected:
                    continue
                if upnode.asnode == self:
                    # dbest announced to itself upnode
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.downpeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                ulist.append(self.announceoriginroute2(upnode, record, ASNUM, n))


        dlist = [True]
        if self.unode.selected:
            # the upnode is selected
            for upnode in self.unode.upnodes:
                # for the upside of the DAG, export best
                if not upnode.selected:
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.uppeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]

#                print("!!!!!!!!!!!!!!!!upnodes of attacker:", self.asid, " announce routes to ", upnet.asid)
                dlist.append(self.announceoriginroute2(upnode, record, ASNUM, n))

        if self.dnode.selected or self.unode.selected:
            return simplify(And(And(ulist), And(dlist)))
        else:
            return True

    # allow AS to announce routes with prepending
    def exportconstraints_prepend(self, dict, ASNUM, link_break = False, opt = False, selected_neighbor = 0):
        # return constraints from export policy
        ulist = [True]
        notlist = []
        if self.dnode.selected:
            # the downnode is selected
            for upnode in self.dnode.upnodes:
                if not upnode.selected:
                    continue
                if upnode.asnode == self:
                    # dbest announced to itself upnode
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.downpeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                if not self.isattacker:
                    # follow a common rule
                    if link_break:
                        # links might break
                        ulist.append(Or(
                            If(self.canexport_d(upnet, ASNUM), self.exportrecord(record, ASNUM, upnode, True),
                               self.emptyinit(record)), self.emptyinit(record)))
                    else:
                        flag = False
                        if opt and upnode.asnode.asid == selected_neighbor:
                            flag = True
                        ulist.append(If(self.canexport_d(upnet, ASNUM),
                                        self.exportrecord_prepend(record, ASNUM, upnode, True, opt=opt, selected = flag),
                                        self.emptyinit(record)))
                else:
                    #                    ulist.append(self.selfconsistent_real(record, ASNUM))
                    ulist.append(self.announceoriginroute(upnode, record, ASNUM))
                    notlist.append(self.emptyinit(record))

        dlist = [True]
        if self.unode.selected:
            # the upnode is selected
            for upnode in self.unode.upnodes:
                # for the upside of the DAG, export best
                if not upnode.selected:
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.uppeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                if not self.isattacker:
                    if link_break:
                        dlist.append(
                            Or(If(self.canexport_u(upnet, ASNUM), self.exportrecord(record, ASNUM, upnode, False),
                                  self.emptyinit(record)), self.emptyinit(record)))
                    else:
                        flag = False
                        if opt and upnode.asnode.asid == selected_neighbor:
                            flag = True
                        dlist.append(If(self.canexport_u(upnet, ASNUM),
                                        self.exportrecord_prepend(record, ASNUM, upnode, False, opt = opt, selected = flag),
                                        self.emptyinit(record)))
                else:
                    #                    dlist.append(self.selfconsistent_real(record, ASNUM))
                    print("!!!!!!!!!!!!!!!!upnodes of attacker:", self.asid, " announce routes to ", upnet.asid)
                    dlist.append(self.announceoriginroute(upnode, record, ASNUM))
                    notlist.append(self.emptyinit(record))

        if self.dnode.selected or self.unode.selected:
            if self.isattacker:
                # attacker will not announce empty route to all neighbors.
                return simplify(And(And(ulist), And(dlist), Not(And(notlist))))
            else:
                return simplify(And(And(ulist), And(dlist)))
        else:
            return True


    def exportconstraints(self, dict, ASNUM, link_break):
        # return constraints from export policy
        ulist = [True]
#        notlist = []
        if self.dnode.selected:
            # the downnode is selected
            for upnode in self.dnode.upnodes:
                if not upnode.selected:
                    continue
                if upnode.asnode == self:
                    # dbest announced to itself upnode
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.downpeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                if not self.isattacker:
                    # follow a common rule
                    if link_break:
                        # links might break
                        ulist.append(Or(If(self.canexport_d(upnet, ASNUM), self.exportrecord(record, ASNUM, upnode, True),
                                           self.emptyinit_r(record)), self.emptyinit_r(record)))
                    else:
                        ulist.append(If(self.canexport_d(upnet, ASNUM), self.exportrecord(record, ASNUM, upnode, True),
                                        self.emptyinit_r(record)))
                else:
                    # explicitedly call for attacker export constraint
#                    print("should not run here!!!!!!!!!!!!!!!!!!!!!")
#                    ulist.append(self.selfconsistent_real(record, ASNUM))
#                    ulist.append(self.announceoriginroute(upnode, record, ASNUM))
                    ulist.append(self.announcecorrectroute(upnode, record, ASNUM))
#                    notlist.append(self.emptyinit(record))
#                ulist.append(self.selfconsistent(record, ASNUM))
#            if not self.isattacker:
#                ulist.append(self.selfconsistent(self.dbest, ASNUM))
#            else:
#                ulist.append(self.selfconsistent_real(self.dbest, ASNUM))
#                ulist.append(record.length > 0)

        dlist = [True]
        if self.unode.selected:
            # the upnode is selected
            for upnode in self.unode.upnodes:
                # for the upside of the DAG, export best
                if not upnode.selected:
                    continue
                upnet = upnode.asnode
                if upnet.asid in self.peers:
                    record = self.uppeerrecords[upnet.asid]
                else:
                    record = self.records[upnet.asid]
                if not self.isattacker:
                    if link_break:
                        dlist.append(Or(If(self.canexport_u(upnet, ASNUM), self.exportrecord(record, ASNUM, upnode, False),
                                        self.emptyinit_r(record)), self.emptyinit_r(record)))
                    else:
                        dlist.append(If(self.canexport_u(upnet,ASNUM), self.exportrecord(record, ASNUM, upnode, False),
                                        self.emptyinit_r(record)))
                else:
#                    dlist.append(self.selfconsistent_real(record, ASNUM))
#                    print("!!!!!!!!!!!!!!!!upnodes of attacker:", self.asid, " announce routes to ", upnet.asid)
                    #dlist.append(self.announceoriginroute(upnode, record, ASNUM))
                    dlist.append(self.announcecorrectroute(upnode, record, ASNUM))
#                    notlist.append(self.emptyinit(record))
#                dlist.append(self.selfconsistent(record, ASNUM))
#            if not self.isattacker:
#                dlist.append(self.selfconsistent(self.best, ASNUM))
#            else:
#                dlist.append(self.selfconsistent_real(self.best, ASNUM))

        if self.dnode.selected or self.unode.selected:
            if self.isattacker:
                # attacker will not announce empty route to all neighbors.
                return simplify(And(And(ulist), And(dlist)))
            else:
                return simplify(And(And(ulist), And(dlist)))
        else:
            return True

    def nexthopiscustomer(self, a, dict):
        # nexthop is customer
        clist = []
        for c in self.customers:
            cnet = dict[c]
            clist.append(a.nexthop == cnet.index)
        if len(clist) > 0:
            aisc = Or(clist)
        else:
            aisc = False
        return aisc


    def nexthopispr(self, a, dict):
        # nexthop is provider or peer
        list = []
        for c in self.providers | self.peers:
            cnet = dict[c]
            list.append(a.nexthop == cnet.index)
        if len(list) > 0:
            aisc = Or(list)
        else:
            aisc = False
        return aisc


    def isorigin(self, a):
        # a is an origin route
        return And(a.aspath == 0, a.length == 0, a.valid == True, a.loc == 100)

    def originroute(self, a):
        # consider the waypoinrt flag
        if self.iswaypoint:
            return And(a.aspath == 0, a.length == 0, a.valid == True, a.loc == 100, a.flag == True)
        else:
            return And(a.aspath == 0, a.length == 0, a.valid == True, a.loc == 100, a.flag == False)


    def comparenexthop(self, a, b, ASNUM):
        # for droute, C,OC > DH
        alist = [False]
        blist = [False]
        for net in self.customers | self.OCpeers:
            if self.dict[net].dnode.selected:
                # change for nexthop
                alist.append(a.aspath == self.dict[net].index)
        for net in self.DHpeers:
            if self.dict[net].dnode.selected:
                # change for nexthop
                blist.append(b.aspath == self.dict[net].index)
        down = And(Or(alist), Or(blist))
        if len(blist) == 1:
            # No DH peers, can not determine the ranking based on the next hop type
            return False
        return If(And(a.droute, b.droute), down, False)

    def equalnexthop(self, a, b, ASNUM):
        # for droute
        alist = [False]
        blist = [False]
        for net in self.customers| self.OCpeers:
            if self.dict[net].dnode.selected:
                # change for nexthop
                alist.append(a.aspath  == self.dict[net].index)
                blist.append(b.aspath  == self.dict[net].index)
        case1 = And(Or(alist), Or(blist))
        alist2 = [False]
        blist2 = [False]
        for net in self.DHpeers:
            if self.dict[net].selected:
                # change for nexthop
                alist2.append(a.aspath == self.dict[net].index)
                blist2.append(b.aspath == self.dict[net].index)
        case2 = And(Or(alist2), Or(blist2))
        # for uroute

        if len(alist) == 1 or len(alist2) == 1:
            # when customers|OCpeers or DHpeers is empty. the next hop has to be the same type. no need to verify
            return True
        return Or(And(a.droute == True, b.droute == True, Or(case1, case2)), And(a.droute == False, b.droute == False))

    def preferover(self, a, b, dict, ASNUM):
        case0 = b.valid == False
        case1 = And(a.valid == True, b.valid==True, a.loc > b.loc)
        case2 = And(a.valid == True, b.valid == True, a.loc == b.loc, a.length < b.length)
        case3 = And(a.valid, b.valid, a.loc == b.loc, a.length == b.length, a.aspath < b.aspath)
        case4 = self.equal(a,b)
        case5 = self.isorigin(a)
        return (Or(case0, case1, case2, case3, case4, case5))

    # generate constraints where route a is preferred or equal to route b
    def preferover_old(self, a, b, dict, ASNUM):
#        samedirection = Or(And(self.nexthopiscustomer(a, dict), self.nexthopiscustomer(b, dict)), And(self.nexthopispr(a, dict), self.nexthopispr(b, dict)))
        case0 = b.valid == False
        # both uphill or downhill
        case1 = And(a.valid == True, b.valid == True, a.droute, Not(b.droute))
        case2 = And(a.valid == True, b.valid == True, a.droute == b.droute, a.backup < b.backup)
        case3 = And(a.valid == True, b.valid == True, a.droute == b.droute, a.backup == b.backup, self.comparenexthop(a, b, ASNUM))
        case4 = And(a.valid == True, b.valid == True, a.droute == b.droute, a.backup == b.backup, self.equalnexthop(a, b, ASNUM), a.length < b.length)
        # change for nexthop
        case5 = And(a.valid == True, b.valid == True, a.droute == b.droute, a.backup == b.backup, self.equalnexthop(a, b, ASNUM), a.length == b.length, a.aspath < b.aspath)
        # customer > provider or peer
#        case2 = And(a.valid == True, b.valid == True, self.nexthopiscustomer(a, dict), self.nexthopispr(b, dict))
        # origin
        case6 = self.isorigin(a)
        case7 = self.equal(a,b)
        return (Or(case0, case1, case2, case3, case4, case5, case6, case7))



#    def samedirection(self, a, b):
        # when both uphill or downhill routes, compare length and asid
        # first prefer shorter route, then prefer smaller nexthop
#        tmp = Or(a.length < b.length, And(a.length == b.length, a.nexthop <= b.nexthop))
#        return tmp


    def originconstraints(self):
        return And(self.originroute(self.best), self.originroute(self.dbest))

    def lowlocpref(self, record, srcasid, dstasid ):
#        loc = (srcasid + dstasid) % 5 + 1
#        return And(record.loc == loc)
        return And(self.neighborloc[srcasid] == record.loc)

    def highlocpref(self, record, srcasid, dstasid):
#        loc = (srcasid + dstasid) % 5 + 6
#        return And(record.loc == loc)
        return And(self.neighborloc[srcasid] == record.loc)


    # set up the contraints only follow the gao-rexford, but not its import policy.
    def importconstraints_bgp(self, dict, ASNUM):

        ulist = [True]
        uorlist = []
        if self.unode.selected:
            # for upside
            if self.dnode.selected:
                uorlist.append(self.equal(self.best, self.dbest))
                ulist.append(If(self.dbest.valid, self.equal(self.dbest, self.best), True))
            for innode in self.unode.downnodes:
                if not innode.selected:
                    continue
                if innode.asnode == self:
                    # innode is itself downnode, ignore
                    continue
                innodenet = innode.asnode
                if innodenet.asid in self.providers:
                    # for innode from providers
                    record = innodenet.records[self.asid]
                else:
                    # for innode from peers
                    if innode.isdownnode:
                        record = innodenet.downpeerrecords[self.asid]
                    else:
                        record = innodenet.uppeerrecords[self.asid]
                # set constraint about the local preference: peer and provider
#                ulist.append(self.lowlocpref(record, innodenet.asid, self.asid))
                ulist.append(And(record.loc >= 0, record.loc <= 100))
                uorlist.append(self.equal(record, self.best))
                ulist.append(self.preferover(self.best, record, dict, ASNUM))
            # always select one incoming route
        if len(uorlist) == 0:
            uselectone = True
        else:
            uselectone = Or(uorlist)

        dlist = [True]
        dorlist = []
        if self.dnode.selected:
            # for downside
            if not self.origin:
                # origin node is already set up
                for innode in self.dnode.downnodes:
                    if not innode.selected:
                        continue
                    innodenet = innode.asnode
                    if innodenet.asid in self.customers:
                        record = innodenet.records[self.asid]
                    else:
                        record = innodenet.downpeerrecords[self.asid]
                    # set constraint about the local preference: customers
#                    ulist.append(self.highlocpref(record, innodenet.asid, self.asid))
                    ulist.append(And(record.loc >= 101, record.loc <= 200))
                    dorlist.append(self.equal(record, self.dbest))
                    dlist.append(self.preferover(self.dbest, record, dict, ASNUM))
        # select one incoming route if it is not origin
        if len(dorlist) > 0:
            dselectone = Or(dorlist)
        else:
            dselectone = True

        if self.dnode.selected or self.unode.selected:
            return simplify(And(Or(uselectone, self.origin), Or(dselectone, self.origin), And(ulist), And(dlist)))
        else:
            return True


    def importconstraints(self, dict, ASNUM):
        ulist = [True]
        uorlist = [self.best.valid == False]
        if self.unode.selected:
            # for upside
            if self.dnode.selected:
                uorlist.append(self.equal(self.best, self.dbest))
                ulist.append(If(self.dbest.valid, self.equal(self.dbest, self.best), True))
            for innode in self.unode.downnodes:
                if not innode.selected:
                    continue
                if innode.asnode == self:
                    # innode is itself downnode, ignore
                    continue
                innodenet = innode.asnode
                if innodenet.asid in self.providers:
                    # for innode from providers
                    record = innodenet.records[self.asid]
                else:
                    # for innode from peers
                    if innode.isdownnode:
                        record = innodenet.downpeerrecords[self.asid]
                    else:
                        record = innodenet.uppeerrecords[self.asid]
                # set constraint about the local preference: peer and provider
                ulist.append(self.lowlocpref(record, innodenet.asid, self.asid))
                uorlist.append(self.equal(record, self.best))
                ulist.append(self.preferover(self.best, record, dict, ASNUM))
            # always select one incoming route
        if len(uorlist) == 0:
            uselectone = True
        else:
            uselectone = Or(uorlist)

        dlist = [True]
        dorlist = [self.dbest.valid == False]
        if self.dnode.selected:
            # for downside
            if not self.origin:
                # origin node is already set up
                for innode in self.dnode.downnodes:
                    if not innode.selected:
                        continue
                    innodenet = innode.asnode
#                    if innodenet.asid in self.customers:
                    # change for journal version: can prefer provider route
                    if innodenet.asid in self.customers | self.providers:
                        record = innodenet.records[self.asid]
                    else:
                        record = innodenet.downpeerrecords[self.asid]
                    # set constraint about the local preference: customers
                    dlist.append(self.highlocpref(record, innodenet.asid, self.asid))
                    dorlist.append(self.equal(record, self.dbest))
                    dlist.append(self.preferover(self.dbest, record, dict, ASNUM))
        # select one incoming route if it is not origin
        if len(dorlist) > 0:
            dselectone = Or(dorlist)
        else:
            dselectone = True

        if self.dnode.selected or self.unode.selected:
            return simplify(And(Or(uselectone, self.origin), Or(dselectone, self.origin), And(ulist), And(dlist)))
        else:
            return True

    def equal(self, a, b):
        return And(a.aspath == b.aspath, a.length == b.length, a.valid == b.valid, a.flag == b.flag, a.loc == b.loc)

    # an non-valid route
    # for dbest and best. the emptylinit can determine locpreference.
    # for r_i_j, the emptyinit should not determine localpreference.
    def emptyinit(self, record):
        return And(record.flag == False, record.aspath == 0, record.length == 0, record.valid == False, record.loc == 0)

    # emptyinit for r_i_j
    def emptyinit_r(self, record):
        return And(record.flag == False, record.aspath == 0, record.length == 0, record.valid == False)

    def record_init(self, topo):
        # generate records for all neighbors.
        # However, when the DAG is considered, some records might not be used
        if self.dnode.selected or self.unode.selected:
            for ulink in self.providers | self.customers:
                ulinknet = topo.idtonet(ulink)
                self.records[ulink] = Record('r_%s_%s' % (self.asid, ulinknet.asid))

            for peer in self.peers:
                peernet = topo.idtonet(peer)
                self.downpeerrecords[peer] = Record('dr_%s_%s' % (self.asid, peernet.asid))
                # change for journal version
#                self.uppeerrecords[peer] = Record('ur_%s_%s' % (self.asid, peernet.asid))

    # add link between ASs and set up local preferences.
    def addrel(self, neighbor, rel):
        if rel == 0:
            self.customers.add(neighbor)
#            self.neighborloc[neighbor] = (neighbor + self.asid) % 2 + 1 # (1, 2)
            self.neighborloc[neighbor] = (neighbor + self.asid) % 1 + 7 # (7, 8)
        elif rel == 2:
            self.peers.add(neighbor)
#            self.neighborloc[neighbor] = (neighbor + self.asid) % 3 + 3 # (3, 4, 5)
            self.neighborloc[neighbor] = (neighbor + self.asid) % 1 + 4 # (4, 5, 6 )
            #if random.random() < self.prefp and \
            if self.violateprefer and not self.violatepreferdone:
                self.neighborloc[neighbor] = 7
                self.violatepreferdone = True
        elif rel == 1:
            self.providers.add(neighbor)
            #            self.neighborloc[neighbor] = (neighbor + self.asid) % 3 + 5 # (5, 6, 7)
            self.neighborloc[neighbor] = (neighbor + self.asid) % 1 + 2  # (2, 3, 4)
            # change for journal version: all possible violation
#            if self.violateprefer and not self.violatepreferdone:
#                self.neighborloc[neighbor] = 7
#                self.violatepreferdone = True
        self.neighbors.add(neighbor)


    # set up self.neighborreceive field
    # called after the whole topo is generated
    def initexportrule(self):
        for n in self.peers:
            self.neighborreceive[n] = set()
            for m in self.peers:
                if n != m:
#                    if random.random() < self.r2r:
                    if self.violateexport and not self.violateexportdone:
                        self.neighborreceive[n].add(m)
                        self.violateexportdone = True
            for m in self.providers:
#                if random.random() < self.p2r:
                if self.violateexport and not self.violateexportdone:
                    self.neighborreceive[n].add(m)
                    self.violateexportdone = True
        for n in self.providers:
            self.neighborreceive[n] = set()
            for m in self.peers:
#                if random.random() < self.r2p:
                if self.violateexport and not self.violateexportdone:
                    self.neighborreceive[n].add(m)
                    self.violateexportdone = True
            # change for journal version: all possible violation
#            for m in self.providers:
#                if self.violateexport and not self.violateexportdone:
#                    self.neighborreceive[n].add(m)
#                    self.violateexportdone = True



    def isisolated(self):
        if len(self.neighbors) < 1:
            return True
        return False

    def getneighbors(self):
        return self.neighbors

    def getpeers(self):
        return self.peers

    def getproviders(self):
        return self.providers

    def getcustomers(self):
        return self.customers