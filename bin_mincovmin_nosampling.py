## OPTIMIZATION 1NAIVE VERSION
# USES STRIPED PARTITIONS
# USES A STACK
# USES ORDERED PARTITIONS
# USES A CACHE OF NON FDS

import csv
import sys
import copy
import random
import argparse
import time
from ae_libs.enumerations import LectiveEnum
from ae_libs.boolean_tree import BooleanTree
from ae_libs.fd_tree import FDTree
from ae_libs.representations import Partition, BottomPairSet, PairSet as Pattern
from ae_libs.fca import FormalContext, next_closure, PreClosure, fast_next_closure
from ae_libs import read_csv
from itertools import product, chain
from collections import defaultdict
from functools import reduce

class Stats(object):
    def __init__(self):
        self.closures = 0
        self.failures = 0
        self.row_check = 0
        self.conflicting_attributes = defaultdict(lambda: 0)
        self.non_conflicting = defaultdict(lambda: 0)

def build_pli(lst):
    '''
    Generates a PLI (position list indexes) given a column in the database (lst) (partition)
    Example:
    [0,1,0,1,1,2] -> [[1,3,4], [0,2]]
    PLIs are ordered by number of indices in each component and filtered of singletons
    '''
    hashes = {}
    for i, j in enumerate(lst):
        hashes.setdefault(j, set([])).add(i)
    return sorted([sorted(i) for i in hashes.values() if len(i) > 1], key = lambda k: len(k), reverse=False)

def attribute_exploration_pps(tuples):
    U = range(len(tuples[0])) # Attributes
    n_atts = len(U) # Number of attributes

    print ("Processing data... ", end='')
    sys.stdout.flush()
    representations = [[row[j] for row in tuples] for j in U]
    print("done")

    plis = [(build_pli(r), ri) for ri, r in enumerate(representations)]
    stats = Stats()

    # ORDERING
    print ("Ordering... ", end='')
    sys.stdout.flush()
    # ATTRIBUTE ORDERING
    plis.sort(key=lambda k: k[0], reverse=False) # Lexicographic
    order = {j[1]:i for i,j in enumerate(plis)} #Original order -> new order
    inv_order = {i:j for j,i in order.items()} # At position i should be attribute j
    patterns = [Pattern.from_lst(representations[inv_order[att]]) for att in range(n_atts)]
    patterns.append( BottomPairSet( Pattern.N_TUPLES) )

    plis = [ i[0] for i in plis ]

    print("done")

    print ("Reconverting... ", end='')
    tuples = [[None]*n_atts for i in range(len(tuples))]
    # print(plis)
    # not_none = [0 for i in range(len(tuples))]

    for att in range(n_atts):
        att = inv_order[att]
        for i, cluster in enumerate(plis[att]):
            for row in cluster:
                tuples[row][att] = i
                
    print("done")
    # # END ORDERING

    Mjs = [set() for i in range(n_atts)] # Needed by fast version of next_closure
    # stack = [[None, None],[None, set([]), Mjs]] # Stack for next_closure
    stack = [[None, patterns[-1], None],[None, None, Mjs]]
    X = set([])
    
    fdt = FDTree(U)
    m_i = -1
    
    cycles = 0
    cycles2 = 0
    XJ = set([])
    
    ncls = 0
    sU = set(U)
    while X != U:
        
        # Feedback Output
        cycles += 1
        if cycles%1 == 0:
            print ("\rFDs:{}/{}".format(fdt.n_fds, cycles),  ','.join(map(str, sorted(X))), end='') #stack
            sys.stdout.flush()

        XJ = stack[-2][1].intersection(patterns[m_i])
        cache = []
        # print(type(XJ))
        XSS = set([m for m in U if m not in X and XJ.leq(patterns[m])])

        if bool(XSS):
            fdt.add_fd(X, XSS)
            stack[-1][-1][m_i] = XSS
        
        if not bool(XSS) or m_i < min(XSS):
            m_i = U[-1]
            X.union(XSS)
        else:
            X.difference_update([m for m in X if m > m_i])

        stack[-1][1] = XJ

        X, m_i = fast_next_closure(X, U, fdt.l_close, m_i, stats, stack)
        # print("\t{} + {}".format(sorted(set(X)-set([m_i])), m_i))
        stack[-1][0] = m_i

    L = list(fdt.read_fds())
    print ("\nN_FDS:{}".format(len(L)))
    print ("CYCLES:",cycles)
    print ("Closures:", ncls)
    print(fdt.recursions)


if __name__ == "__main__":
    
    __parser__ = argparse.ArgumentParser(description='FD Miner - Sampling-based Version')
    __parser__.add_argument('database', metavar='database_path', type=str, help='path to the formal database')
    __parser__.add_argument('-s', '--separator', metavar='separator', type=str, help='Cell separator in each row', default=',')
    # __parser__.add_argument('-p', '--use_patterns', help='Use Pattern Structures for DB', action='store_true')
    __parser__.add_argument('-i', '--ignore_headers', help='Ignore Headers', action='store_true')
    args = __parser__.parse_args()

    tuples = read_csv(args.database, separator=args.separator)
    
    t0 = time.time()
    attribute_exploration_pps(tuples)
    print ("TIME: {}s".format(time.time()-t0))

