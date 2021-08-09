from verifier import *
import pickle

import getopt
from topo import *
import random
import numpy as np


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

def createfilename(oprefix):
    prefix = "../topos/small"
    suffix = ".txt"
    rst = []
    for i in range(50, 1050, 50):
        infile = prefix + str(i) + suffix
        outfile = oprefix + str(i) + suffix
        rst.append((infile, outfile))
    return rst


# select hijack candidate and store into file
# select three nodes for each query: origin, victim, attacker
def hijackcandidate(num = 10):
    files = createfilename("../topos/hijack")
    for ifile, outfile in files:
        candlists = []
        topo = Topo(ifile)
        keys = topo.dict.keys()
        for i in range(0, num):
            threenodes = set()
            while len(threenodes) < 3:
                key = random.choice(keys)
                if key not in threenodes:
                    threenodes.add(key)
            threenodeslist = list(threenodes)
            candlists.append(threenodeslist)
        with open(outfile, "w") as f:
            pickle.dump(candlists, f)



def itecandidatepertopo(opts, args, num = 10, output = "./ITE_n_candidate.txt"):
        rst = {}
        rsys = Verifier(opts, args, False)
        VICTIM = 15169
        counter = 0
        rrs = []
        for asid, node in rsys.topo.dict.iteritems():
            if asid != VICTIM and asid not in rsys.topo.dict[VICTIM].neighbors and len(node.neighbors) >= 2:
                ORIGIN = asid
                rsys.topo.topotrim(ORIGIN, VICTIM, ORIGIN)
                neighbors = []
                for n in node.neighbors:
                    if rsys.isselected(n):
                        neighbors.append(n)
                rr = rsys.topo.trimstat()
                rrs.append(rr)
                rsys.clear()
                if len(neighbors) >= 2:
                    rst[asid] = neighbors
                    counter += 1
            if counter >= num:
                break
        print("ITE_neighbor candidate:", rst)
        with open(output, "w") as f:
            pickle.dump(rst, f)

        std = np.std(rrs)
        # 101 samples, 99% confidence intervals double sides
        alpha = 2.626
        rrci = alpha * std / np.sqrt(len(rrs) - 1)
        print("mean:", np.mean(rrs))
        print("rrci:", rrci)
        return rst


def itecandidate(num=10, smallscale = True):
    if smallscale:
        for i in range(600, 700, 100):
            opts = [("-r", "../topos/15169small" + str(i) + ".txt")]
            output = "../topos/15169ite" + str(i) + ".txt"
            itecandidatepertopo(opts, None, num = num, output=output)
    else:
        for i in range(2003, 2023, 5):
            opts = [("-r", "../topos/" + str(i) + "0501.as-rel.txt")]
            output = "../topos/15169_year" + str(i) + "ite.txt"
            itecandidatepertopo(opts, None, num = num, output = output)



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



    numpertopo = 101
    #hijackcandidate(num = numpertopo)

    itecandidate(num = numpertopo, smallscale=True)





if __name__ == '__main__':
    sys.exit(main())