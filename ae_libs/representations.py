import random
import sys
import csv
from itertools import combinations, product
from math import factorial as fac
from ae_libs.boolean_tree import BooleanTree



def binomial(x, y):
    print "BINOMIAL", x, y
    try:
        binom = fac(x) // fac(y) // fac(x - y)
    except ValueError:
        binom = 0
    return binom
'''
************************************************************************************************
HANDLES THE KIND OF REPRESENTATION
************************************************************************************************
'''
class Top(object):
    @staticmethod
    def intersection(other):
        return other
    @staticmethod
    def add(obj):
        pass
    @staticmethod
    def is_empty():
        return False
    @staticmethod
    def update(obj):
        pass


class Representation(object):
    '''
    Abstract representation
    '''
    def __init__(self, desc):
        self.desc = desc
    def intersection(self, other):
        raise NotImplementedError
    def leq(self, other):
        raise NotImplementedError
    def sample(self, lst):
        raise NotImplementedError
    def __repr__(self):
        return str(self.desc)
    def __sub__(self, other):
        raise NotImplementedError
    def pick_sample_from_difference(self, other, samples):
        raise NotImplementedError
    def add(self, value):
        self.desc.add(value)
    def update(self, obj):
        self.desc.update(obj)
    def is_top(self):
        raise NotImplementedError

class Partition(Representation):
    '''
    Partiton representation, split partitions
    list of sets
    '''
    N_TUPLES = 0
    def __init__(self, desc):
        '''
        Sort and split the partition
        '''
        self.idx = None
        desc = [i for i in desc if len(i) > 1]
        desc.sort(key=lambda k: (len(k), min(k)), reverse=True)
        if len(desc) == 0:
            desc.append(set([]))
        super(Partition, self).__init__(desc)
        self._nparts = None
    @property
    def nparts(self):
        if self._nparts is None:
            self._nparts = len(self.desc) + Partition.N_TUPLES - (sum([len(i) for i in self.desc]))
        return self._nparts
        
    def set_idx(self, idx):
        self.idx = idx

    @staticmethod
    def from_lst(lst):
        Partition.N_TUPLES = max(len(lst), Partition.N_TUPLES)
        hashes = {}
        for i, j in enumerate(lst):
            hashes.setdefault(j, set([])).add(i)
        return Partition(hashes.values())

    def intersection(self, other):
        '''
        Procedure STRIPPED_PRODUCT defined in [1]
        '''
        new_desc = []
        T = {}
        S = {}
        for i, k in enumerate(self.desc):
            for t in k:
                T[t] = i
            S[i] = set([])
        
        for i, k in enumerate(other.desc):
            for t in k:
                if T.get(t, None) is not None:
                    S[T[t]].add(t)
            for t in k:
                if T.get(t, None) is not None:
                    if len(S[T[t]]) > 1:
                        new_desc.append(S[T[t]])
                    S[T[t]] = set([])

        return Partition(new_desc)


    def leq(self, other, cache):
        '''
        Procedure STRIPPED_PRODUCT defined in [1]
        '''
        if len(self.desc) == 1 and len(self.desc[0]) == 0:
            return True
        # if other.nparts > self.nparts:
        #     return False
        T = {}

        for i, k in enumerate(other.desc):
            for t in k:
                T[t] = i
        
        for i, k in enumerate(self.desc):
            
            it = iter(k)
            ti = next(it)
            

            mvalue = T.get(ti, -1)
            fpair = [ti]
            for ti in it:
                if T.get(ti, -2) != mvalue:
                    fpair.append(ti)
                    cache.append(tuple(fpair))
                    
                    return False
        return True


    # def leq(self, other, cache):
    #     # print self.nparts, other.nparts
    #     if other.nparts > self.nparts:
    #         return False
    #     for i in self.desc:
    #         go_on = False
    #         for j in other.desc:
    #             if len(i) > len(j):
    #                 return False
    #             if i.issubset(j):
    #                 go_on=True
    #                 break
    #         if not go_on:
    #             return False
    #     return True
    #     # for i in self.desc:
    #     #     if not any(i.issubset(j) for j in other.desc):
    #     #         return False
    #     # return True

    def sample(self, sample):
        sampled = set([])
        for i, j in sample:
            for s in self.desc:
                if i in s and j in s:
                    sampled.add((i,j))
                    break
                elif i in s or j in s:
                    break
        return sampled


    def pick_sample_from_difference(self, other, samples):
        # print "PICK", self, other, samples
        
        for s1 in self.desc:
            for i, j in combinations(s1, 2):
                if any(i in s2 and j in s2 for s2 in other.desc):
                    continue
                else:
                    t = (i,j) if i<j else (j,i)
                    samples.append(t)
                    return t
        # print samples
        # exit()
        # samples.append(next(iter(self.desc - other.desc)))
    def is_empty(self):
        return len(self.desc) == 1 and len(self.desc[0]) == 0

    def __eq__(self, other):
        if len(self.desc) != len(other.desc):
            return False
        for s in self.desc:
            if any(s == j for j in other.desc):
                continue
            else:
                return False
        return True
    def is_top(self):
        if len(self.desc) == 1 and len(self.desc[0]) == Partition.N_TUPLES:
            return True
        return False
    

class PairSet(Representation):
    '''
    Pairset representation, set of tuple pairs
    '''
    N_TUPLES = 0
    @staticmethod
    def from_lst(lst):
        '''
        Generates the set of pairs from a list of elements
        [1,2,1,2] generates the pairs [(0,2), (1,3)]
        Actually, pairs are the transitive closure of the equivalence relation
        '''
        Pairset.N_TUPLES = max(len(lst), Pairset.N_TUPLES)
        hashes = {}
        for i, j in enumerate(lst):
            hashes.setdefault(j, set([])).add(i)
        desc = set([])
        for val in hashes.values():
            map(desc.add, combinations(sorted(val), 2))
        return PairSet(desc)
        

    def intersection(self, other):
        return PairSet(self.desc.intersection(other.desc))

    def leq(self, other):
        return self.desc.issubset(other.desc)

    def sample(self, sample):
        return PairSet(self.desc.intersection(sample))

    def pick_sample_from_difference(self, other, samples):
        samples.append(next(iter(self.desc - other.desc)))

    # def is_top(self):
    #     return len(self.desc) == binomial(PairSet.N_TUPLES, 2)
        
    


'''
************************************************************************************************
HANDLES THE DATABASE AND SAMPLING
************************************************************************************************
'''


class Database(object):
    def __init__(self):
        self._data = None
        self._partitions = None
        self._ps = None
        self._atts = None
        self._ctx = None
        self._n_tuples = None
        self.TRep = PairSet
        
        # self._representation_method = lst_to_pairs
        # self._representation_method = lst_to_partitions
    @property
    def n_atts(self):
        return len(self.ctx)

    @property
    def n_tuples(self):
        if self._n_tuples is None:
            self._n_tuples = len(self._data)
        return self._n_tuples

    def read_csv(self, path, separator=',', has_headers=False, quotechar='"'):
        '''
        Read csv into self._data
        self._data contains the original parsed file
        '''
        self._data = []
        with open(path, 'r') as csvfile:
            reader = csv.reader(csvfile, delimiter=separator, quotechar=quotechar)
            for line in reader:
                self._data.append(map(str, line))
        if has_headers:
            del self._data[0]
        
        # print self._data

    @property
    def ctx(self):
        '''
        Returns the context and builds it if its not been built yet.
        The context is simply the self._data transposed
        '''
        if self._ctx is None:
            self._ctx = [[row[j] for row in self._data] for j in range(len(self._data[0]))]
        return self._ctx

    @property
    def partitions(self):
        '''
        Builds the partitions from the context
        partitions can be either a list of pairs or a list of sets.
        '''
        if self._partitions is None:
            self._partitions = [self.TRep.from_lst(j) for j in self.ctx]
            # self._partitions = [filter(lambda x:len(x)>1, lst_to_pairs(j)) for j in self.ctx]
        # print self._partitions
        return self._partitions

    @property
    def ps(self):
        if self._ps is None:
            self._ps =  {i: j for i, j in enumerate(self.partitions)}
        return self._ps

    @property
    def atts(self):
        if self._atts is None:
            self._atts = range(len(self.ctx))
        return self._atts

    def get_top_atts(self):
        for i, j in self.ps.items():
            if j.is_top():
                yield i 


class Expert(Database):
    def __init__(self, stack):
        Database.__init__(self)
        self.sample = set([])
        self._real_ps = None
        self.increments = 0
        self._smap = None
        self.TExpert = Partition
        self.stack = stack

    @property
    def sample_map(self):
        if self._smap is None:
            self._smap = list(range(self.n_tuples))
            random.shuffle(self._smap)
        return self._smap

    
    def get_next_pair(self):
        for i, j in combinations(list(range(self.n_tuples)), 2):
            
            yield (self.sample_map[i], self.sample_map[j]) if self.sample_map[i] < self.sample_map[j] else (self.sample_map[j], self.sample_map[i])

    @property
    def partitions(self):
        '''
        Builds the partitions from the context
        partitions can be either a list of pairs or a list of sets.
        '''
        if self._partitions is None:
            self._partitions = [self.TExpert.from_lst(j) for j in self.ctx]
            # self._partitions = [filter(lambda x:len(x)>1, lst_to_pairs(j)) for j in self.ctx]
        # print self._partitions
        return self._partitions

    @property
    def ps(self):
        '''
        Returns the sampeld object representations
        '''
        
        if self._ps is None:
            # self.possible_pairs = self.n_tuples**2/2-self.n_tuples/2
            # self.sample_size = int(self.possible_pairs*self.split)
            self.sample = []
            self._real_ps = {i: j for i, j in enumerate(self.partitions)}
            self._ps =  {i: self.TRep(j.sample(self.sample)) for i, j in enumerate(self.partitions)}
        
        return self._ps
    

    def check_bk(self, preintent, preextent):        
        new_extent = reduce(lambda x, y: x.intersection(y), (self._real_ps[i] for i in preintent)) #A^I
        new_intent = set([i for i, j in self._real_ps.items() if i not in preintent and new_extent.leq(j)]) # A^II
        new_intent.update(preintent)
        return new_intent, new_extent

    def check(self, new_att, prevint, closed_preintent, prevAI):
        
        if prevAI.is_empty():
            '''
            Search up the stack if there is a pattern we can partially use
            to calculate the current one. In the worst case, we will always
            use the top.
            '''
            for idx in range(len(self.stack)-1, -1, -1):
                if not self.stack[idx][2].is_empty():
                    break
            prevAI.desc = self.stack[idx][2].intersection(
                reduce(
                    lambda x, y: x.intersection(y),
                    (self._real_ps[i] for i in sorted(prevint, reverse=True) if i not in self.stack[idx][0])
                )
            ).desc #A^I

        AI = prevAI.intersection(self._real_ps[new_att])
        cache = []
        AII = set([j for j in closed_preintent if AI.leq(self._real_ps[j], cache)]) # AII complement
        # for i, j in cache:
        #     match = [self._data[i][att]==self._data[j][att] for att in range(self.n_atts) ]
        #     self.non_fds.append(match)
        # print cache
        return AII, AI


    def increment_sample(self, AI, AII, closed_preintent, preintent, preextent):
        
        # print ''
        # print AI
        # print '\t',closed_preintent, AII

        self.increments += 1

        
        # it = iter(sorted(closed_preintent - AII, key=lambda k: len(self._ps[k].desc), reverse=True))
        it = sorted(closed_preintent - AII, reverse=True)#, key=lambda k: len(self._ps[k].desc), reverse=True))
        # random.shuffle(it)
        it = iter(it)
        # print sorted([(len(self._ps[i].desc) , i) for i in closed_preintent - AII], reverse=False)
        # print closed_preintent - AII
        go_on = True
        while go_on:
            # NOTICE THAT THE NEXT ITERATOR SHOULD NEVER REACH STOPITERATOR EXCEPTION
            sample_target = next(it)
            
            new_point = None

            # REVERSED AS PARTITIONS ARE SORTED FROM LARGER TO SMALLER COMPONENTS
            # SMALLER COMPONENTS HAVE A BETTER CHANCE OF BEING UNIQUE TO THE PARTITION
            for s1 in reversed(AI.desc):
                s1 = list(s1)
                random.shuffle(s1)
                for i, j in combinations(s1, 2):

                    choose = True
                    if (i,j) in self.sample:
                        choose=False
                        continue
                    for s2 in self._real_ps[sample_target].desc:
                        if i in s2 and j in s2:
                            choose = False
                            break
                        elif i in s2 or j in s2:
                            break
                    if choose:
                        break
                    # if any(i in s2 and j in s2 for s2 in reversed(self._real_ps[sample_target].desc)):
                    #     continue
                if choose:
                    new_point = (i,j) if i<j else (j,i)
                    go_on = False
                    break
                # if new_point is not None:
                #     break
        # print '\t\t NEW POINT:', (i,j) 
        self.sample.append(new_point)
        self._ps =  {i: self.TRep(j.sample(self.sample)) for i, j in enumerate(self.partitions)}
        
        
        return new_point
    
    def get_top_atts(self):
        ps = self.ps
        for i, j in self._real_ps.items():
            if j.is_top():
                yield i 


class ExpertPartitionSampler(Expert):
    '''
    Uses partition pattern structures for checking and providing counterexamples.
    More efficient with large number of rows and sparse database.
    '''
    def __init__(self, stack):
        super(ExpertPartitionSampler, self).__init__(stack)
        self.non_fds = BooleanTree()
        self.cache = []

    def check(self, new_att, prevint, closed_preintent, prevAI, preintent):
        '''
        Checks if closed_preintent is correct using the real database.
        This check is performed using pattern structures.
        Returns AII, the actual closed_preintent, and AI, the pattern structure
        of the preintent
        '''
        x = len([i for i in self.stack if i[2] is None])
        
        sys.stdout.flush()
        if self.stack[-1][2] is None:
            '''
            Search up the stack if there is a pattern we can partially use
            to calculate the current one. In the worst case, we will always
            use the top.
            '''
            # print [i[2] for i in self.stack]
            for idx in range(len(self.stack)-1, -1, -1):
                if self.stack[idx][2] is not None:
                    break
            # print prevAI, type(prevAI)
            # exit()
            # print '\n::', idx
            for si in range(idx+1, len(self.stack)):
                # print '\t =>', si
                self.stack[si][2] = self.stack[si-1][2].intersection(
                    reduce(
                        lambda x, y: x.intersection(y),
                        # (self._real_ps[i] for i in sorted(self.stack[si][0], reverse=True) if i not in self.stack[si-1][0])
                        (self._real_ps[i] for i in self.stack[si][0].difference(self.stack[si-1][0]))
                    )
                )
        prevAI = self.stack[-1][2]

        AI = prevAI.intersection(self._real_ps[new_att])
        
        sys.stdout.flush()
        AII = set([])
        match = [True]*self.n_atts
        self.cache = []
        old_cache_size = 0
        
        for j in closed_preintent:
            if match[j] and AI.leq(self._real_ps[j], self.cache): # AII complement
                AII.add(j)
            if len(self.cache) > old_cache_size:
                old_cache_size = len(self.cache)
                i, j = self.cache[-1]
                match2 = [self._data[i][att]==self._data[j][att] for att in range(self.n_atts) ]

                for att in range(self.n_atts):
                    match[att] = match[att] and match2[att]
                self.non_fds.append(match2)
                self.non_fds.append(match)

        return AII, AI  

    def increment_sample(self, AI, AII, closed_preintent, preintent, preextent):
        self.increments += 1
        # negative_atts = closed_preintent - AII
        # print '\n'
        # print negative_atts, self.cache
        # if bool(self.cache):
        new_points = []
        while bool(self.cache):
            i,j = self.cache.pop()
        # i,j  = self.cache.pop()
        # print self.cache
            new_point = (i,j) if i<j else (j,i)

            self.sample.append(new_point)
            match = [self._data[i][att]==self._data[j][att] for att in range(self.n_atts) ]

            for i in (a for a, t in enumerate(match) if t):
                self._ps[i].desc.add(new_point)
            new_points.append(new_point)
        
        return new_points


    def increment_sample_bk(self, AI, AII, closed_preintent, preintent, preextent):
        """
        Called in the case AII is not equal to closed_preintent
        Samples a pair of tuples that takes some attribute in closed_preintent - AII
        out of closed_preintent.
        This is done by re-sampling the formal context.
        """
        self.increments += 1

        negative_atts = closed_preintent - AII

        signatures = {}
        idx = {}
        for h in range(self.n_tuples):
            ti = self.sample_map[h]
            row = self._data[ti]
            left = tuple([row[att] for att in preintent])
            right = tuple([row[att] for att in negative_atts])
            sign = signatures.get(left, None)
            if sign is None:
                signatures[left] = right
                idx[left] = ti
            elif sign != right:
                i = ti
                j = idx[left]
                new_point = (i,j) if i<j else (j,i)
                match = [self._data[i][att]==self._data[j][att] for att in range(self.n_atts) ]
                self.non_fds.append(match)
                break
        self._smap = self._smap[h:] + self._smap[:h]

        self.sample.append(new_point)

        for i in (a for a, t in enumerate(match) if t):
            self._ps[i].desc.add(new_point)
        
        return [new_point]


    @property
    def partitions(self):
        '''
        Builds the partitions from the context
        partitions can be either a list of pairs or a list of sets.
        '''
        if self._partitions is None:
            self._partitions = [self.TExpert.from_lst(j) for j in self.ctx]
            
            map(lambda (i, p): p.set_idx(i), enumerate(self._partitions))
            orden = lambda p: (self.n_tuples-sum([len(j) for j in p.desc]))+len(p.desc)
            
            self._partitions.sort(key=orden)
            for ti, t in enumerate(self._data):
                new_t = [None]*len(t)
                for i, j in enumerate(t):
                    new_t[i] = t[self._partitions[i].idx]
                for i, j in enumerate(new_t):
                    self._data[ti][i] = j

        return self._partitions

class ExpertLinearSampler(Expert):
    '''
    Based on linear iterations of the column values,
    heavily influenced by [1].
    Most efficient when the number of rows is not very high
    and the number of FDs in the database is low.
    '''
    def __init__(self, stack):
        super(ExpertLinearSampler, self).__init__(stack)
        self.non_fds = BooleanTree()
        self.cache = []

    def check_bk(self, new_att, prevint, closed_preintent, prevAI):
        
        if prevAI.is_empty():
            '''
            Search up the stack if there is a pattern we can partially use
            to calculate the current one. In the worst case, we will always
            use the top.
            '''
            for idx in range(len(self.stack)-1, -1, -1):
                if not self.stack[idx][2].is_empty():
                    break
            prevAI.desc = self.stack[idx][2].intersection(
                reduce(
                    lambda x, y: x.intersection(y),
                    (self._real_ps[i] for i in sorted(prevint, reverse=True) if i not in self.stack[idx][0])
                )
            ).desc #A^I

        AI = prevAI.intersection(self._real_ps[new_att])
        
        AII = set([])
        match = [True]*self.n_atts
        self.cache = []
        old_cache_size = 0
        # print '\n',
        # print "CHECKING", closed_preintent
        for j in closed_preintent:
            # print '\t', j
            if match[j] and AI.leq(self._real_ps[j], self.cache): # AII complement
                
                AII.add(j)
            # print '\t\t=>', self.cache
            if len(self.cache) > old_cache_size:
                old_cache_size = len(self.cache)
                i, j = self.cache[-1]
                match2 = [self._data[i][att]==self._data[j][att] for att in range(self.n_atts) ]
                for att in range(self.n_atts):
                    match[att] = match[att] and match2[att]
                self.non_fds.append(match2)

        return AII, AI

    def check(self, new_att, prevint, closed_preintent, prevAI, preintent):
        signatures = {}
        tuple_map = {}
        # preintent = prevint + [new_att]
        preintent = sorted(preintent)
        members = sorted(closed_preintent)
        AII = set(range(len(closed_preintent)))
        
        
        for h in range(self.n_tuples):
            ti = self.sample_map[h]
            row = self._data[ti]
            left = tuple([row[att] for att in preintent])
            right = tuple([row[att] for att in members])
            sign = signatures.get(left, None)
            if sign is None:
                signatures[left] = right
                tuple_map[left] = ti
            elif any(sign[idx] != right[idx] for idx in AII):
                i = ti
                j = tuple_map[left]
                new_point = (i,j) if i<j else (j,i)
                match = [self._data[i][att]==self._data[j][att] for att in range(self.n_atts) ]
                self.non_fds.append(match)
                self.cache.append(new_point)

                map(AII.remove, [att for att in AII if sign[att] != right[att]])

            if not bool(AII):
                break
        AII = set([members[idx] for idx in AII])

        return AII, None


    def increment_sample(self, AI, AII, closed_preintent, preintent, preextent):
        self.increments += 1
        negative_atts = closed_preintent - AII
        # print '\n'
        # print negative_atts, self.cache
        # if bool(self.cache):
        new_points = []
        while bool(self.cache):
            i,j = self.cache.pop()
        # i,j  = self.cache.pop()
        # print self.cache
            new_point = (i,j) if i<j else (j,i)

            self.sample.append(new_point)
            match = [self._data[i][att]==self._data[j][att] for att in range(self.n_atts) ]

            for i in (a for a, t in enumerate(match) if t):
                self._ps[i].desc.add(new_point)
            new_points.append(new_point)
        
        return new_points
        # else:
        #     return [self.increment_sample_bk(AI, AII, closed_preintent, preintent, preextent)]
    @property
    def partitions(self):
        '''
        Builds the partitions from the context
        partitions can be either a list of pairs or a list of sets.
        '''
        if self._partitions is None:
            self._partitions = [self.TExpert.from_lst(j) for j in self.ctx]
            
            map(lambda (i, p): p.set_idx(i), enumerate(self._partitions))
            orden = lambda p: (self.n_tuples-sum([len(j) for j in p.desc]))+len(p.desc)
            
            self._partitions.sort(key=orden)
            
            for ti, t in enumerate(self._data):
                
                new_t = [None]*len(t)
                for i, j in enumerate(t):
                    new_t[i] = t[self._partitions[i].idx]
                for i, j in enumerate(new_t):
                    self._data[ti][i] = j

        return self._partitions