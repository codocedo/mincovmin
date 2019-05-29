import sys
from random import randint

class AddIntentAlgorithm(object):
    def __init__(self):
        self.top = None
        self.supremum = 0
        self.infimum = 0
        self.lat = [[]]
        self.inv_lat = [[]]
        self.objects = {}
        self.jip_objects = []
        self.elements = [None]
    def add_object(self, obj, nid):
        self.objects[obj] = nid
        self.jip_objects.append(obj)

    def get_jips(self):
        for i, j in enumerate(self.inv_lat):
            if len(j) == 1:
                yield i
    def non_jip_objects(self):
        result = []
        for o in self.jip_objects:
            if len(self.inv_lat[self.objects[o]]) > 1:
                result.append(o)
        for o in result:
            self.jip_objects.remove(o)
        return result
            

    def get_maximal_generator(self, intent, current_generator):
        """
        Given an intent, we explore the lattice and obtain the unique formal concept
        the intent of which subsumes the intent. We call this the maximal concept.
        """
        # If the given intent is empty (or is the bottom intent),
        # the maximal concept in the lattice is the supremum
        # print('---')
        # print(intent, current_generator)
        # print (self.lat)
        # print (self.elements)
        # print(self.supremum)
        if current_generator == self.supremum or not bool(intent):# self.pattern.is_empty(intent):
            return self.supremum

        for super_concept in self.lat[current_generator]:
            # THE CONCEPT ALREADY EXISTS. RETURN THE NODE ID OF THAT CONCEPT
            if intent == self.elements[super_concept]: #   self.pattern.is_equal(self.lat[super_concept].intent, intent):
                return super_concept
            # THE MOST COMMON CASE
            elif intent.issubset(self.elements[super_concept]):# self.pattern.leq(intent, self.lat[super_concept].intent):
                return self.get_maximal_generator(intent, super_concept)
        return current_generator

    def add_intent_iteration(self, intent, generator=0, depth=1):
        """
        A single add_intent iteration
        intent: intent to add
        generator: current concept
        depth: internal
        """
        # print(generator)
        generator = self.get_maximal_generator(intent, generator)
        # print(generator)
        if generator != self.infimum and self.elements[generator] == intent:
            # print('x', intent)
            return generator
        
        new_parents = []
        for candidate in self.lat[generator]:
            if not self.elements[candidate].issubset(intent):
                cand_inter = set.intersection(self.elements[candidate], intent)
                candidate = self.add_intent_iteration(cand_inter, candidate, depth+1)

            add_parent = True
            for parent in new_parents:
                if self.elements[candidate].issubset(self.elements[parent]):
                # if self.pattern.leq(self.lat[candidate].intent, self.lat[parent].intent):
                    add_parent = False
                    break
                elif self.elements[parent].issubset(self.elements[candidate]):
                # elif self.pattern.leq(self.lat[parent].intent, self.lat[candidate].intent):
                    new_parents.remove(parent)
                    # del new_parents[new_parents.index(parent)]
            if add_parent:
                new_parents.append(candidate)

        new_id = len(self.elements)
        # print ('\t +', intent, generator)
        self.elements.append(intent)
        self.lat.append([])
        self.inv_lat.append([])
        # self.objects.append([])
        
        # new_id = self.lat.new_formal_concept(copy.copy(self.lat[generator].extent), intent)

        for parent in new_parents:
            if parent in self.lat[generator]:
                self.lat[generator].remove(parent)
                self.inv_lat[parent].remove(generator)
                # self.lat.remove_edge(generator, parent)

            self.lat[new_id].append(parent)
            self.inv_lat[parent].append(new_id)

        self.lat[generator].append(new_id)
        self.inv_lat[new_id].append(generator)
        # self.lat.add_edge(generator, new_id)
        if self.supremum == generator:
            self.supremum = new_id
        # exit()
        return new_id

if __name__ == "__main__":
    alg = AddIntentAlgorithm()
    collection = [
        {12, 11, 13, 7},
        {13, 8, 10, 7, 4, 3},
        {4, 7, 11, 8, 9, 5},
        {9, 11, 5, 4, 13, 6, 3},
        {7, 3, 4, 12, 2}
    ]


    # n_atts = randint(5,20)
    for x in collection:
        # x = set([randint(1,n_atts) for i in range(randint(2, 10))])
        print('ADDING', x)
        alg.add_intent_iteration(x, 0)
    print(alg.elements)
    print(alg.lat)
    print(alg.inv_lat)
    print (alg.supremum)