'''
[1] Papenbrock et al - A Hybrid Approach to Functional Dependency Discovery (2016)
'''
import logging

logger = logging.getLogger(__name__)

class FDCollection(object):
    def __init__(self, n_atts):
        self.n_atts = n_atts
    def add(self, lhs, rhss):
        raise NotImplementedError
    def l_close(self, pat):
        raise NotImplementedError
    @property
    def n_fds(self):
        raise NotImplementedError
    def read_fds(self):
        raise NotImplementedError

class FDList(FDCollection):
    def __init__(self, n_atts):
        super(FDList, self).__init__(n_atts)
        self.L = []
    def add(self, lhs, rhss):
        self.L.append( (lhs, rhss) )
    def l_close(self, pat):
        newpat = set(pat)
        
        complement = set([])
        while True:
            if len(newpat) == self.n_atts:
                break
            subparts = [con for ant, con in self.L if len(ant) < len(newpat) and ant.issubset(newpat)]
            if bool(subparts):
                complement = reduce(set.union, subparts)
                if complement.issubset(newpat):
                    break
                else:
                    newpat.update(complement)
            else:
                break
        return newpat
    @property
    def n_fds(self):
        return len(self.L)
    def read_fds(self):
        for i in self.L:
            yield i

class FDOList(FDList):
    def add(self, lhs, rhss):
        super(FDOList, self).add(lhs, rhss)
        self.L.sort(key = lambda (lhs, rhs):  len(lhs))
        # i=0
        # for i, (olhs, orhs) in enumerate(self.L):
        #     if len(olhs) <= len(lhs):
        #         break
        # self.L.insert(i, (lhs, rhss))
        # print self.L
    def l_close(self, pat):
        newpat = set(pat)
        
        complement = set([])
        while True:
            if len(newpat) == self.n_atts:
                break
            subparts = []
            for ant, con in self.L:
                if len(newpat) <= len(ant):
                    break
                if len(ant) < len(newpat) and ant.issubset(newpat):
                    subparts.append(con)
                
            # subparts = [con for ant, con in self.L ]
            if bool(subparts):
                complement = reduce(set.union, subparts)
                if complement.issubset(newpat):
                    break
                else:
                    newpat.update(complement)
            else:
                break
        return newpat
        
    
class FDNode(object):
    def __init__(self, att=-1, n_atts=0):
        self.att = att
        # self.idx = [True]*n_atts
        self.link = {}
        self.parent = None
        self._rhs=[False]*n_atts
        self.active = False
    
    def set_rhss(self, rhss):
        for i in rhss:
            self._rhs[i] = True
        self.active = True

    
    def get_children(self):
        for i in sorted(self.link.keys()):
            yield self.link[i]

    def invalidate(self, invalid_rhss):
        for i in invalid_rhss:
            self._rhs[i] = False

    def __repr__(self):
        return str("<FDNode>{}=>{}".format(self.get_lhs(), str(self.get_rhss())))

    def get_rhss(self):
        return [i for i, j in enumerate(self._rhs) if j]

    def get_lhs(self):
        base = set([self.att])
        parent = self.parent
        while parent is not None:
            if parent.att>=0:
                base.add(parent.att)
            parent = parent.parent
        return base

    def flip(self):
        for i in range(len(self._rhs)):
            self._rhs[i] = not self._rhs[i]

    def add_child(self, child):
        # self.idx[child.att] = False
        self.link[child.att] = child
        child.parent = self


class FDTree(FDCollection):
    '''
    Keeps a set of FDs stored in a tree.
    Implemented using descriptions found in [1]
    '''
    def __init__(self, n_atts=0):
        '''
        Initializes the object by setting the number of attributes
        contained in the functional dependencies to be stored.
        The tree only holds a reference to the root node.
        '''
        super(FDTree, self).__init__(n_atts)
        self.root = FDNode(n_atts=self.n_atts)
        self._n_fds = 0

    def _level_and_recurse(self, current_node, sought_depth, depth=0):
        '''
        Recursive function searching within the tree
        for all nodes at a given depth.
        Nodes do not store information on its depth
        so the depth is calculated along with the navigation
        by means of the depth parameter

        
        current_node -- FDNode, Current node in the navigation
        sought_depth -- int, Target depth
        depth -- int, current depth (default 0)
        '''
        if sought_depth == depth:
            yield current_node
        else:
            for att in sorted(current_node.link.keys()):
                for i in self._level_and_recurse(current_node.link[att], sought_depth, depth+1):
                    yield i

    def get_level(self, sought_depth):
        '''
        Yields all nodes at a given depth by means

        sought_depth -- int, Target depth
        '''
        for i in self._level_and_recurse(self.root, sought_depth):
            yield i

    def _print_and_recurse(self, current_node, depth=1):
        '''
        Recursively print the nodes in the tree

        current_node -- FDNode, current node in the navigation
        depth -- int current depth
        '''
        print '\t'*depth, current_node.att, current_node.rhs, current_node.link
        for i in sorted(current_node.link.keys()):
            self._print_and_recurse(current_node.link[i], depth+1)

    def print_tree(self):
        '''
        Print all nodes in the tree
        '''
        self._print_and_recurse(self.root)
    
    def find_fd(self, lhs, rhs):
        '''
        Search in the FDTree for the FD lhs -> rhs
        lhs -- set with attribute ids in the left hand side
        rhs -- attribute id in the right hand side
        '''
        current_node = self.root
        s_lhs = sorted(lhs, reverse=True)
        while bool(s_lhs):
            next_att = s_lhs.pop()
            if current_node.link.get(next_att, False):
                current_node = current_node.link[next_att]
            else:
                return False
        return current_node.rhs[rhs]

    def _find_and_recurse(self, current_node, lhs):
        
        if current_node.active:
            yield current_node.get_rhss()

        if not bool(lhs) or not bool(current_node.link) or max(current_node.link.keys()) < lhs[-1]:
            return
        for ati, att in enumerate(lhs):
            next_node = current_node.link.get(att, False)
            if next_node:
                for fd in self._find_and_recurse(next_node, lhs[ati:]):
                    yield fd
        # for att in sorted(current_node.link.keys()):
        #     if att in lhs:
        #         next_node = current_node.link[att]
        #         for i in self._find_and_recurse(next_node, base.union([att]), lhs):
        #             yield i
            # elif att < lhs[-1]:
            #     break

    def find_rhss(self, lhs):
        '''
        Search in the FDTree for the FD lhs -> rhs
        lhs -- set with attribute ids in the left hand side
        rhs -- attribute id in the right hand side
        '''
        
        if len(lhs) == self.n_atts:
            return
        # print "LHS", lhs
        slhs = sorted(lhs, reverse=True)
        for old_rhs in self._find_and_recurse(self.root,  slhs):
            # print '\t\t',old_lhs, old_rhs
            yield old_rhs
        # print "--"
        # return False

        

    def add(self, lhs, rhss):
        """
        Adds a set of FDs to the tree of the form
        lhs -> rhs for each rhs in rhss

        lhs -- set of attribute ids in the left hand side
        rhss -- set of attribute ids in the right hand side
        """

        new_node = None
        current_node = self.root
        s_lhs = sorted(lhs,reverse=False)
        self._n_fds += 1

        while bool(s_lhs):
            next_att = s_lhs.pop()
            add = True
            if current_node.link.get(next_att, False):
                current_node = current_node.link[next_att]
            else:
                new_node = FDNode(att=next_att, n_atts=self.n_atts)
                current_node.add_child(new_node)
                current_node = new_node
        current_node.set_rhss(rhss)
        
        return new_node

    def _read_and_recurse(self, current_node, lhs):
        '''
        Recursively read all FDs in the FDTree

        current_node -- current node in the navigation
        lhs -- current left hand side
        '''
        if current_node.active:
            yield (lhs, current_node.get_rhss())

        for att in sorted(current_node.link.keys()):
            next_node = current_node.link[att]
            for fd in self._read_and_recurse(next_node, lhs.union([att])):
                yield fd
            

    def read_fds(self):
        '''
        Read all fds in the FDTree
        '''
        current_node = self.root
        base = set([])
        for i in self._read_and_recurse(current_node, base):
            yield i

    def check_and_recurse(self, current_node, base, lhs, rhs):
        
        if base.issubset(lhs) and current_node.rhs[rhs]:
            yield (base, rhs)
        for att in sorted(current_node.link.keys()):
            if att in lhs:
                next_node = current_node.link[att]
                for i in self.check_and_recurse(next_node, base.union([att]), lhs, rhs):
                    yield i
            elif att > max(lhs):
                break
        
    def fd_has_generals(self, lhs, rhs):
        """
        rhs contains a single attribute
        """
        base = set([])
        result = False
        for old_lhs, old_rhs in self.check_and_recurse(self.root, base, lhs, rhs):
            result = True
            break
        return result

    def get_fd_and_generals(self, lhs, rhs):
        base = set([])
        for old_lhs, old_rhs in self.check_and_recurse(self.root, base, lhs, rhs):
            yield old_lhs

    def remove(self, lhs, rhs):
        '''
        Remove FD lhs->rhs from the FDTree

        '''
        self._n_fds -= 1
        current_node = self.root
        s_lhs = sorted(lhs,reverse=True)
        while bool(s_lhs):
            next_att = s_lhs.pop()
            if current_node.link.get(next_att, False):
                current_node = current_node.link[next_att]
            else:
                raise KeyError
        
        current_node.rhs[rhs] = False
    def l_close(self, pat):
        newpat = set(pat)

        while True:
            complement = reduce(set.union, [set([])]+[rhs for rhs in self.find_rhss(newpat)])
            if complement.issubset(newpat):
                break
            newpat.update(complement)
        return newpat
    @property
    def n_fds(self):
        return self._n_fds