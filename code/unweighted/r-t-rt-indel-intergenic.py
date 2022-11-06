# encoding: utf-8

import math
import sys
import random
import itertools
import time


DEBUG = False


#####################################################################
################## REPRESENTS A NODE OF A GRAPH #####################
#####################################################################

class cycle_graph_node :

    def __init__(self, index, padded) :
        #index  : stores the black edge i, 0 <= i <= n+1
        #value  : stores pi_i
        self.index, self.value    = index, 0        
        self.padded   = padded
        self.cycle    = 0
        ## Kind:
        ## 0 = unset
        ## 1 = small cycle             (1)
        ## 2 = oriented    convergent  (3, 1, 2)
        ## 3 = even        convergent  (2,  1)
        ## 4 = even        divergent   (2, -1)
        ## 5 = nonoriented convergent  (3, 2, 1)
        ## 6 = oriented    divergent   (3,-2,-1), (3,1,-2), (3,-1, 2)
        ## 7 = nonoriened  divergent   (3,2,-1),  (3,-2,1), (3,-1,-2)
        self.kind     = 0

        ## 0 = unset 
        ## i = num of black edges
        self.size        = 0 

        ## 0   = unset or balanced
        ## +-i = (gray - black) weights
        self.blacks      = 0
        self.grays       = 0
        self.gray_labeled     = False
        self.black_labeled    = False

        ## 0 = unset
        ## 1 = convergent
        ## 2 = divergent
        self.direction = 0

        #ap     : points to the record that stores pi_{i-1}, 1 <= i <= n+1
        #ab     : points to the record that stores pi_{i+1}, 0 <= i <= n
        #ac     : points to the record that stores i + 1,    0 <= i <= n
        self.ap, self.ab, self.ac = 0,0,0

        #visit  : indicates if the record has been visited
        self.visit  = False

        ## when gray or black edges are labeled, we will list the
        ## sizes of all intergenic regions between them. if the
        ## len(wc) = lc + 1 and len(wp) = lp + 1
        self.wc                   = [0,]
        self.wp                   = [0,]
        self.wcs                  = 0
        self.wps                  = 0
        self.lc                   = 0
        self.lc_iota              = []
        self.lp                   = 0

############################################################################
############ Do not need to represent a real permutation ###################
############################################################################

## This class represents an unoriented cycle-graph. Keep in mind that
## this class is not the same as used for the sorting by transposition
## problem. Here, the white edges are not the reverse of the black
## edges as before. That is because the black edges can go from righ
## to left as well as to left to right.

## For instance, assume a permutation (5, 2, ...). The configuration
## in the graph would be.

## node(0).ap  = -5      ## node(0).ab  = Null
## node(-5).ab = 5       ## node(-5).ap = 0  
## node(5).ap  = -2      ## node(5).ab  = -5 
## node(-2).ab = 2       ## node(-2).ap = 5

class cycle_configuration_graph() :
    def __init__(self, cycles,
                 weight_gray ,
                 weight_black,
                 final_length) :

        # With different content we do not need to check this
        #if (sum(weight_gray) != sum(weight_black)) :
        #    print("Different intergenic regions")
        #    sys.exit()


        ## The number of cycles was never calculated
        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.__first_indice_shift   = 0 # Tell us the index of the
                                        # edge that is pointed by
                                        # begin_node. If it is
                                        # negative, than we know that
                                        # a mirror have occurred.

        ## self.n is the number of black edges. Remember this graph
        ## might not be a permutation
        self.n = 0
        self.final_n = final_length
        for cycle in cycles :
            self.n = self.n + len(cycle)
        n = self.n
          
        # Creating nodes
        node_list = []
        node_list = [cycle_graph_node(i, False) for i in range(2*n)]
        self.begin_node = node_list[0 ]
        self.end_node   = node_list[-1]

        # Creating ap
        for i in range(0,2*n,2) :
            node_list[i  ].ap  = node_list[i+1]
            node_list[i+1].ap  = node_list[i  ]
            weight = weight_black[int(i/2)]
            node_list[i  ].wp  = node_list[i+1].wp  = weight
            
            node_list[i  ].wps  = weight[0]
            node_list[i+1].wps  = weight[0]
            if len(weight) > 1 :
                node_list[i  ].wps  += weight[-1]
                node_list[i+1].wps  += weight[-1]

            node_list[i  ].lp  = len(weight)-1
            node_list[i+1].lp  = len(weight)-1

        # Creating ab
        for i in range(1,2*n-1,2) :
            node_list[i  ].ab  = node_list[i+1]
            node_list[i+1].ab  = node_list[i  ]

        # Creating ac 
        for cycle in cycles :
            for i in range(len(cycle)) :               
                front, back  = -1,-1 # from left of the black edge.
                j = (i+1)%len(cycle)

                if cycle[i] > 0 :
                    front = 2*( cycle[i]  -1 )
                else :
                    front = 2*(-cycle[i]) -1

                if cycle[j] > 0 :
                    back = 2*( cycle[j]) -1
                else :
                    back = 2*(-cycle[j]  -1 )

                #print(front, back)
                node_list[front].ac = node_list[back]
                node_list[back].ac  = node_list[front]

        self.set_values()
        for i in range(0,2*n,1) :
            positive =  min(abs(node_list[i].value),
                            abs(node_list[i].ac.value))
            
            weight = weight_gray[positive]
            node_list[i].wc     = weight
            node_list[i].ac.wc  = weight

            node_list[i].wcs     = weight[0]
            node_list[i].ac.wcs  = weight[0]
            if len(weight) > 1 :
                node_list[i].wcs     += weight[-1]
                node_list[i].ac.wcs  += weight[-1]
            node_list[i].lc     = node_list[i].ac.lc  = len(weight)-1

        insert_iota1 = node_list[0]
        insert_iota2 = insert_iota1.ac
        curr = 1

        insert_iota1.lc_iota = [i for i in range(curr,curr+insert_iota1.lc)]
        insert_iota2.lc_iota = insert_iota1.lc_iota
        
        curr += insert_iota1.lc+1
        insert_iota1 = insert_iota2.ab
        insert_iota2 = insert_iota1.ac

        while True :
            insert_iota1.lc_iota = [i for i in range(curr,curr+insert_iota1.lc)]
            insert_iota2.lc_iota = insert_iota1.lc_iota
            
            curr += insert_iota1.lc+1
            
            insert_iota1 = insert_iota2.ab
            if insert_iota1 == 0 :
                break
            else :
                insert_iota2 = insert_iota1.ac


    ############################################################                
    ################ Rearrangement Operations  #################
    ############################################################ 
    # transposition when model has no indels
    def transposition(self, i, j, k, weight_i, weight_j, weight_k) :
        node_i = None
        node_j = None
        node_k = None

        unp_i, unp_j, unp_k = 0,0,0

        count     = 0
        unp_count = 0

        node = self.begin_node
        # Find the black edges
        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j :
                node_j = node
                unp_j  = unp_count
            if count == k :
                node_k = node
                unp_k  = unp_count
            node = node.ap.ab
        
        if (weight_i <  0 or weight_i > node_i.wp) :
            print("ERRO: Peso inconsistente no lado esquerdo: i (max = %s: w = %s)" % (
                node_i.wp,
                weight_i
            ) )
            sys.exit()

        if (weight_j < 0 or weight_j > node_j.wp) :
            print("ERRO: Peso inconsistente no meio:  j (max = %s: w = %s)" % (
                node_j.wp,
                weight_j
            ) )
            sys.exit()

        if (weight_k < 0 or weight_k > node_k.wp) :
            print("ERRO: Peso inconsistente no lado direito:  k (max = %s: w = %s)" % (
                node_k.wp,
                weight_k
            ) )
            sys.exit()


        ## Weights that will be exchanged.
        lefti, righti = weight_i, node_i.wp - weight_i
        leftj, rightj = weight_j, node_j.wp - weight_j
        leftk, rightk = weight_k, node_k.wp - weight_k
            
        # Change the edges
        node_i.ap.ap = node_k
        node_j.ap.ap = node_i
        node_k.ap.ap = node_j

        
        aux       = node_i.ap
        node_i.ap = node_j.ap
        node_j.ap = node_k.ap
        node_k.ap = aux

        # Updating weights: Node_i keeps its place, Node_j moved to
        # the third black edge and Node_k is now in the middle.
        node_i.wp = node_i.ap.wp = lefti  + rightj
        node_k.wp = node_k.ap.wp = righti + leftk
        node_j.wp = node_j.ap.wp = rightk + leftj

        #print "novospesos %d %d %d" % (node_i.wp, node_k.wp, node_j.wp)
        
        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.reset_indices()
        return unp_i, unp_j, unp_k
        
    def transposition2(self, i, j, k, new_weight_i, new_weight_j, new_weight_k) :
        node_i = None
        node_j = None
        node_k = None

        unp_i, unp_j, unp_k = 0,0,0

        count     = 0
        unp_count = 0

        node = self.begin_node
        # Find the black edges
        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j :
                node_j = node
                unp_j  = unp_count
            if count == k :
                node_k = node
                unp_k  = unp_count
            node = node.ap.ab
            
        # Change the edges
        node_i.ap.ap = node_k
        node_j.ap.ap = node_i
        node_k.ap.ap = node_j

        
        aux       = node_i.ap
        node_i.ap = node_j.ap
        node_j.ap = node_k.ap
        node_k.ap = aux

        # Updating weights: Node_i keeps its place, Node_j moved to
        # the third black edge and Node_k is now in the middle.
        node_i.wp = node_i.ap.wp = new_weight_i
        node_k.wp = node_k.ap.wp = new_weight_j
        node_j.wp = node_j.ap.wp = new_weight_k

        
        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.reset_indices()
        return unp_i, unp_j, unp_k
    
    # reversal when model has no indels
    def reversal(self, i, j, weight) :
        node_i = None
        node_j = None

        unp_i, unp_j = 0,0

        count     = 0
        unp_count = 0
        ## These variables are used to return the transposition
        ## applied as integer. ret_i, and ret_j will be the same
        ## as i,j if we do not have ignored black edges
        node = self.begin_node
        # Find the black edges

        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j+1 :
                node_j = node
                unp_j  = unp_count - 1
            node = node.ap.ab


        if (weight >  0 and weight > node_i.wp) :
            print("ERRO: Peso inconsistente no lado esquerdo: i (max = %s: w = %s)" % (
                node_i.wp,
                weight
            ) )
            sys.exit()

        if (weight < 0 and abs(weight) > node_j.wp) :
            print("ERRO: Peso inconsistente no lado direito:  j (max = %s: w = %s)" % (
                node_j.wp,
                weight
            ) )
            sys.exit()

        nweight_i = node_i.wp - weight
        nweight_j = node_j.wp + weight            
            
        # Change the edges
        node_i.ap.ap = node_j.ap
        node_i.ap.wp = nweight_j        
        node_j.ap.ap = node_i.ap
        node_j.ap.wp = nweight_j        

        node_i.ap  = node_j
        node_i.wp  = nweight_i        
        node_j.ap  = node_i
        node_j.wp  = nweight_i

        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.__num_balanced_cycles  = False                
        self.reset_indices()
        return unp_i, unp_j

    # reversal when model has indels
    def reversal2(self, i, j, x, y, nweight_i, nweight_j) :
        node_i = None
        node_j = None

        unp_i, unp_j = 0,0

        count     = 0
        unp_count = 0
        ## These variables are used to return the reversal
        ## applied as integer. ret_i, and ret_j will be the same
        ## as i,j if we do not have ignored black edges
        node = self.begin_node
        # Find the black edges

        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j+1 :
                node_j = node
                unp_j  = unp_count - 1
            node = node.ap.ab


        if (x < 0) or (x > sum(node_i.wp)) :
            print("ERRO: Peso inconsistente no lado esquerdo: i (max = %s: w = %s)" % (
                sum(node_i.wp),
                str(x)
            ) )
            sys.exit()

        if (y < 0) or (y > sum(node_j.wp)) :
            print("ERRO: Peso inconsistente no lado direito:  j (max = %s: w = %s)" % (
                sum(node_j.wp),
                str(y)
            ) )
            sys.exit()         



        # Reverse all wp's greater than one between them
        if node_i.index > node_j.index :
            if node_i.index > node_i.ap.index :
                max_reverse_list = node_i.ap.ab
            else :
                max_reverse_list = node_i.ab
            if node_j.index > node_j.ap.index :
                min_reverse_list = node_j.ab
            else :
                min_reverse_list = node_j.ap.ab
        else :
            if node_j.index > node_j.ap.index :
                max_reverse_list = node_j.ap.ab
            else :
                max_reverse_list = node_j.ab
            if node_i.index > node_i.ap.index :
                min_reverse_list = node_i.ab
            else :
                min_reverse_list = node_i.ap.ab

        while min_reverse_list.index <= max_reverse_list.index :
            if len(min_reverse_list.wp) > 1 :
                min_reverse_list.wp = min_reverse_list.ap.wp = min_reverse_list.wp[::-1]
            min_reverse_list = min_reverse_list.ap.ab


        # Change the black edges
        
        node_i.ap.ap = node_j.ap
        node_j.ap.ap = node_i.ap
        node_i.ap.wp = node_j.ap.wp = nweight_j

        node_i.ap  = node_j
        node_j.ap  = node_i
        node_i.wp  = node_j.wp  = nweight_i

        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.__num_balanced_cycles  = False                
        self.reset_indices()
        return unp_i, unp_j

    def indel(self, is_insertion, i, x, elements, intergenic_regions) :
        node_i = None
        unp_i = 0

        count     = 0
        unp_count = 0
        ## These variables are used to return the indel
        ## applied as integer. ret_i will be the same
        ## as i if we do not have ignored black edges

        node = self.begin_node
        # Find the black edges

        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            node = node.ap.ab

        if (x > sum(node_i.wp)) :
            print("ERRO: Posicao da delecao superior ao tamanho total da regiao intergenica: (wp = %s: del = %s: pos_x_size = %s)" % (
                str(node_i.wp),
                str(intergenic_regions),
                str(x)
            ) )
            sys.exit()

        # let us check in which position of wp the indel will affect
        position_x = 0
        curr_pos_x_size = node_i.wp[0]

        while (curr_pos_x_size < x) :
            position_x += 1
            curr_pos_x_size += node_i.wp[position_x]

        if is_insertion :
            if len(elements) == 0 : # just add some size to the intergenic region
                node_i.wp[position_x] = node_i.ap.wp[position_x] = node_i.wp[position_x] + intergenic_regions[0]
                ####node_i.wps = node_i.wp[0]
                ####if len(node_i.wp) > 1 :
                ####    node_i.wps += node_i.wp[-1]
                ####node_i.ap.wps = node_i.wps
                ####node_i.blacks = node_i.ap.blacks = node_i.wps

            else : # add sizes in between and also intergenic regions. this step is applied only
                   # on trivial cycles, otherwise it must be modified to work with non-trivial cycles.
                if node_i.size == 1 :
                    number_of_new_nodes = 2*len(elements)
                    self.n += len(elements)
                    new_nodes = [cycle_graph_node(i, False) for i in range(number_of_new_nodes)]

                    left_weight_orig = x
                    right_weight_orig = node_i.wp[0] - x

                    left_wc_orig = node_i.wc[0]
                    right_wc_orig = node_i.wc[-1]

                    # create new black and gray edges of unitary cycles
                    j = 1
                    for i in range(1,number_of_new_nodes-1,2) :
                        new_nodes[  i].ap = new_nodes[  i].ac = new_nodes[i+1]
                        new_nodes[i+1].ap = new_nodes[i+1].ac = new_nodes[  i]

                        new_nodes[  i].size = new_nodes[i+1].size = 1

                        new_nodes[  i].blacks = new_nodes[  i].wps = intergenic_regions[j]
                        new_nodes[i+1].blacks =  new_nodes[i+1].wps = intergenic_regions[j]
                        new_nodes[  i].wp = new_nodes[i+1].wp = [intergenic_regions[j],]

                        new_nodes[  i].grays = new_nodes[  i].wcs = node_i.wc[j]
                        new_nodes[i+1].grays = new_nodes[i+1].wcs = node_i.wc[j]
                        new_nodes[  i].wc = new_nodes[i+1].wc = [node_i.wc[j],]

                        new_nodes[  i].lc = len(new_nodes[  i].wc)-1
                        new_nodes[  i].lp = len(new_nodes[  i].wp)-1
                        new_nodes[i+1].lc = len(new_nodes[i+1].wc)-1
                        new_nodes[i+1].lp = len(new_nodes[i+1].wp)-1

                    # create white edges between new edges
                    for i in range(0,number_of_new_nodes-1,2) :
                        new_nodes[  i].ab = new_nodes[i+1]
                        new_nodes[i+1].ab = new_nodes[  i]

                    # link new edges in the extremities with the old ones
                    new_nodes[ 0].ap = new_nodes[ 0].ac = node_i
                    new_nodes[-1].ap = new_nodes[-1].ac = node_i.ac
                    node_i.ac.ap = node_i.ac.ac = new_nodes[-1]
                    node_i.ac = node_i.ap = new_nodes[0]

                    new_nodes[ 0].blacks    = new_nodes[ 0].wps    = left_weight_orig + intergenic_regions[0]
                    new_nodes[ 0].ap.blacks = new_nodes[ 0].ap.wps = left_weight_orig + intergenic_regions[0]
                    new_nodes[ 0].wp = new_nodes[ 0].ap.wp = [int(left_weight_orig + intergenic_regions[0]),]

                    new_nodes[ 0].grays    = new_nodes[ 0].wcs    = left_wc_orig
                    new_nodes[ 0].ac.grays = new_nodes[ 0].ac.wcs = left_wc_orig
                    new_nodes[ 0].wc = new_nodes[ 0].ac.wc = [left_wc_orig,]

                    new_nodes[-1].blacks    = new_nodes[-1].wps    = right_weight_orig + intergenic_regions[-1]
                    new_nodes[-1].ap.blacks = new_nodes[-1].ap.wps = right_weight_orig + intergenic_regions[-1]
                    new_nodes[-1].wp = new_nodes[-1].ap.wp = [int(right_weight_orig + intergenic_regions[-1]),]

                    new_nodes[-1].grays    = new_nodes[-1].wcs    = right_wc_orig
                    new_nodes[-1].ac.grays = new_nodes[-1].ac.wcs = right_wc_orig
                    new_nodes[-1].wc = new_nodes[-1].ac.wc = [right_wc_orig,]

                    new_nodes[ 0].lc    = len(new_nodes[ 0].wc)-1
                    new_nodes[ 0].lp    = len(new_nodes[ 0].wp)-1
                    new_nodes[ 0].ac.lc = len(new_nodes[ 0].ac.wc)-1
                    new_nodes[ 0].ap.lp = len(new_nodes[ 0].ap.wp)-1
                    new_nodes[-1].lc    = len(new_nodes[-1].wc)-1
                    new_nodes[-1].lp    = len(new_nodes[-1].wp)-1
                    new_nodes[-1].ac.lc = len(new_nodes[-1].ac.wc)-1
                    new_nodes[-1].ap.lp = len(new_nodes[-1].ap.wp)-1

                    self.set_values()

                else : # here we consider a cycle of size 2
                    number_of_new_nodes0 = number_of_new_nodes2 = 0
                    new_nodes0 = new_nodes2 = None
                    if elements[0] and elements[1] :
                        number_of_new_nodes = 2 * len(elements[0]) + 2 * len(elements[1])
                        self.n += len(elements[0]) + len(elements[1])
                        new_nodes = [cycle_graph_node(i, False) for i in range(number_of_new_nodes)]

                        # create new black and gray edges of unitary cycles
                        j, k = 1, 1
                        for i in range(1,number_of_new_nodes-1,2) :
                            new_nodes[  i].ap = new_nodes[  i].ac = new_nodes[i+1]
                            new_nodes[i+1].ap = new_nodes[i+1].ac = new_nodes[  i]

                            new_nodes[  i].size = new_nodes[i+1].size = 1

                            new_nodes[  i].blacks = new_nodes[  i].wps = intergenic_regions[j]
                            new_nodes[i+1].blacks = new_nodes[i+1].wps = intergenic_regions[j]
                            new_nodes[  i].wp     = new_nodes[i+1].wp  = [intergenic_regions[j]]

                            if i < (2 * len(elements[0]) -1) :
                                curr_gray = node_i.wc[j]
                            else :
                                curr_gray = node_i.ac.ap.wc[k]
                                k += 1

                            new_nodes[  i].grays = new_nodes[  i].wcs = curr_gray
                            new_nodes[i+1].grays = new_nodes[i+1].wcs = curr_gray
                            new_nodes[  i].wc    = new_nodes[i+1].wc  = [curr_gray,]

                            new_nodes[  i].lc = len(new_nodes[  i].wc)-1
                            new_nodes[i+1].lc = len(new_nodes[i+1].wc)-1
                            new_nodes[  i].lp = len(new_nodes[  i].wp)-1
                            new_nodes[i+1].lp = len(new_nodes[i+1].wp)-1

                            j += 1

                        # create white edges between new edges
                        for i in range(0,number_of_new_nodes-1,2) :
                            new_nodes[  i].ab = new_nodes[i+1]
                            new_nodes[i+1].ab = new_nodes[  i]

                        # link new edges in the extremities with the old ones
                        node_left_left   = node_i.ap.ac        # +a
                        node_left_right  = node_left_left.ap   # -b
                        node_right_left  = node_i              # +c
                        node_right_right = node_i.ap           # -d
                        new_first_left   = new_nodes[0]
                        new_last_left    = new_nodes[2*len(elements[0])]
                        new_first_right  = new_nodes[2*len(elements[0])-1]
                        new_last_right   = new_nodes[-1]

                        gray_weights_helper = [node_left_left.wc[0], node_left_left.wc[-1], node_right_left.wc[0], node_right_left.wc[-1]]

                        # node_left_left   will link with new_first_left  > trivial
                        # node_left_right  will link with new_last_right  > trivial
                        # node_right_left  will link with new_last_left   > 2-cycle
                        # node_right_right will link with new_first_right > 2-cycle

                        # left trivial cycle
                        # black and gray edges
                        new_first_left.ap = new_first_left.ac = node_left_left
                        node_left_left.ap = node_left_left.ac = new_first_left
                        # black edges weight
                        new_first_left.blacks = new_first_left.wps = intergenic_regions[0]
                        node_left_left.blacks = node_left_left.wps = intergenic_regions[0]
                        new_first_left.wp     = node_left_left.wp  = [intergenic_regions[0],]
                        # gray edges weight
                        new_first_left.grays = new_first_left.wcs = gray_weights_helper[0]
                        node_left_left.grays = node_left_left.wcs = gray_weights_helper[0]
                        new_first_left.wc    = node_left_left.wc  = [gray_weights_helper[0],]

                        # right trivial cycle
                        # black and gray edges
                        new_last_right.ap = new_last_right.ac = node_left_right
                        node_left_right.ap = node_left_right.ac = new_last_right
                        # black edges weight
                        if type(intergenic_regions[-1]) == int :
                            new_last_right.blacks = new_last_right.wps = intergenic_regions[-1]
                            node_left_right.blacks = node_left_right.wps = intergenic_regions[-1]
                            new_last_right.wp     = node_left_right.wp  = [intergenic_regions[-1]]
                        else :
                            new_last_right.blacks = new_last_right.wps = intergenic_regions[-1][0] + intergenic_regions[-1][-1]
                            node_left_right.blacks = node_left_right.wps = intergenic_regions[-1][0] + intergenic_regions[-1][-1]
                            new_last_right.wp     = node_left_right.wp  = intergenic_regions[-1]
                        # gray edges weight
                        new_last_right.grays = new_last_right.wcs = gray_weights_helper[3]
                        node_left_right.grays = node_left_right.wcs = gray_weights_helper[3]
                        new_last_right.wc    = node_left_right.wc  = [gray_weights_helper[3],]

                        # 2-cycle
                        # setting gray edges, sice black edges were already set
                        node_right_left.ac  = new_last_left
                        new_last_left.ac    = node_right_left
                        node_right_right.ac = new_first_right
                        new_first_right.ac  = node_right_right
                        # setting its black edges weights
                        if len(new_first_right.wp) > 1 :
                            new_first_right.wps = new_last_left.wps = new_first_right.wp[0] + new_first_right.wp[-1]
                        else :
                            new_first_right.wps = new_last_left.wps = new_first_right.wp[0]
                        new_last_left.blacks    = node_right_left.blacks = new_last_left.wps + node_right_right.wps
                        node_right_right.blacks = new_first_right.blacks = new_last_left.wps + node_right_right.wps
                        # setting its gray edges weights
                        node_right_left.grays  = node_right_left.wcs  = gray_weights_helper[2]
                        new_last_left.grays    = new_last_left.wcs    = gray_weights_helper[2]
                        node_right_left.wc     = new_last_left.wc     = [gray_weights_helper[2],]
                        node_right_right.grays = node_right_right.wcs = gray_weights_helper[1]
                        new_first_right.grays  = new_first_right.wcs  = gray_weights_helper[1]
                        node_right_right.wc    = new_first_right.wc   = [gray_weights_helper[1],]

                        # label flags for left trivial cycle
                        node_left_left.lc = len(node_left_left.wc)-1
                        new_first_left.lc = len(new_first_left.wc)-1
                        node_left_left.lp = len(node_left_left.wp)-1
                        new_first_left.lp = len(new_first_left.wp)-1

                        # label flags for right trivial cycle
                        node_left_right.lc = len(node_left_right.wc)-1
                        new_last_right.lc  = len(new_last_right.wc)-1
                        node_left_right.lp = len(node_left_right.wp)-1
                        new_last_right.lp  = len(new_last_right.wp)-1

                        # label flags for the 2-cycle
                        node_right_left.lc  = len(node_right_left.wc)-1
                        new_last_left.lc    = len(new_last_left.wc)-1
                        node_right_right.lc = len(node_right_right.wc)-1
                        new_first_right.lc  = len(new_first_right.wc)-1
                        node_right_left.lp  = len(node_right_left.wp)-1
                        new_last_left.lp    = len(new_last_left.wp)-1
                        node_right_right.lp = len(node_right_right.wp)-1
                        new_first_right.lp  = len(new_first_right.wp)-1

                        self.set_values()

                    elif elements[0] :
                        number_of_new_nodes = 2 * len(elements[0])
                        self.n += len(elements[0])
                        new_nodes = [cycle_graph_node(i, False) for i in range(number_of_new_nodes)]

                        # create new black and gray edges of unitary cycles
                        j = 1
                        for i in range(1,number_of_new_nodes-1,2) :
                            new_nodes[  i].ap = new_nodes[  i].ac = new_nodes[i+1]
                            new_nodes[i+1].ap = new_nodes[i+1].ac = new_nodes[  i]

                            new_nodes[  i].size = new_nodes[i+1].size = 1

                            new_nodes[  i].blacks = new_nodes[  i].wps = intergenic_regions[j]
                            new_nodes[i+1].blacks = new_nodes[i+1].wps = intergenic_regions[j]
                            new_nodes[  i].wp     = new_nodes[i+1].wp  = [intergenic_regions[j]]

                            new_nodes[  i].grays = new_nodes[  i].wcs = node_i.wc[j]
                            new_nodes[i+1].grays = new_nodes[i+1].wcs = node_i.wc[j]
                            new_nodes[  i].wc    = new_nodes[i+1].wc  = [node_i.wc[j],]

                            new_nodes[  i].lc = len(new_nodes[  i].wc)-1
                            new_nodes[i+1].lc = len(new_nodes[i+1].wc)-1
                            new_nodes[  i].lp = len(new_nodes[  i].wp)-1
                            new_nodes[i+1].lp = len(new_nodes[i+1].wp)-1

                            j += 1

                        # create white edges between new edges
                        for i in range(0,number_of_new_nodes-1,2) :
                            new_nodes[  i].ab = new_nodes[i+1]
                            new_nodes[i+1].ab = new_nodes[  i]

                        # link new edges in the extremities with the old ones
                        node_left_left   = node_i.ap.ac        # +a
                        node_left_right  = node_left_left.ap   # -b
                        node_right_left  = node_i              # +c
                        node_right_right = node_i.ap           # -d
                        new_first        = new_nodes[0]        # -e
                        new_last         = new_nodes[-1]       # +e

                        gray_weights_helper = [node_left_left.wc[0], node_left_left.wc[-1]]

                        # link new edges in the extremities with the old ones
                        # trivial cycle, black and gray edges
                        new_first.ap      = new_first.ac      = node_left_left
                        node_left_left.ac = node_left_left.ap = new_first
                        # trivial cycle, black edges weights
                        new_first.blacks      = new_first.wps      = intergenic_regions[0]
                        node_left_left.blacks = node_left_left.wps = intergenic_regions[0]
                        new_first.wp          = node_left_left.wp  = [intergenic_regions[0],]
                        # trivial cycle, gray edges weights
                        new_first.grays      = new_first.wcs      = gray_weights_helper[0]
                        node_left_left.grays = node_left_left.wcs = gray_weights_helper[0]
                        new_first.wc         = node_left_left.wc  = [gray_weights_helper[0],]
                        # trivial cycle, label flags
                        new_first.lc      = len(new_first.wc)-1
                        node_left_left.lc = len(node_left_left.wc)-1
                        new_first.lp      = len(new_first.wp)-1
                        node_left_left.lp = len(node_left_left.wp)-1

                        # non-trivial cycle, black and gray edges
                        new_last.ap         = node_left_right
                        node_left_right.ap  = new_last
                        new_last.ac         = node_right_right
                        node_right_right.ac = new_last
                        # non-trivial cycle, black edges
                        new_last.wp             = node_left_right.wp     = intergenic_regions[-1]
                        if len(new_nodes[-1].wp) > 1 :
                            new_last.wps = node_left_right.wps = new_nodes[-1].wp[0] + new_nodes[-1].wp[-1]
                        else :
                            new_last.wps = node_left_right.wps = new_nodes[-1].wp[0]
                        new_last.blacks         = node_left_right.blacks = new_last.wps + node_right_right.wps
                        node_right_right.blacks = node_right_left.blacks = new_last.wps + node_right_right.wps
                        # non-trivial cycles, gray edges
                        new_last.grays         = new_last.wcs         = gray_weights_helper[1]
                        node_right_right.grays = node_right_right.wcs = gray_weights_helper[1]
                        new_last.wc            = node_right_right.wc  = [gray_weights_helper[1],]
                        # non-trivial cycle, label flags
                        new_last.lc         = len(new_last.wc)-1
                        node_left_right.lc  = len(node_left_right.wc)-1
                        node_right_right.lc = len(node_right_right.wc)-1
                        node_right_left.lc  = len(node_right_left.wc)-1
                        new_last.lp         = len(new_last.wp)-1
                        node_left_right.lp  = len(node_left_right.wp)-1
                        node_right_right.lp = len(node_right_right.wp)-1
                        node_right_left.lp  = len(node_right_left.wp)-1

                        self.set_values()

                    else : # only elements[1]
                        number_of_new_nodes = 2 * len(elements[1])
                        self.n += len(elements[1])
                        new_nodes = [cycle_graph_node(i, False) for i in range(number_of_new_nodes)]

                        # create new black and gray edges of unitary cycles
                        j = 1
                        for i in range(1,number_of_new_nodes-1,2) :
                            new_nodes[  i].ap = new_nodes[  i].ac = new_nodes[i+1]
                            new_nodes[i+1].ap = new_nodes[i+1].ac = new_nodes[  i]

                            new_nodes[  i].size = new_nodes[i+1].size = 1

                            new_nodes[  i].blacks = new_nodes[  i].wps = intergenic_regions[j]
                            new_nodes[i+1].blacks = new_nodes[i+1].wps = intergenic_regions[j]
                            new_nodes[  i].wp     = new_nodes[i+1].wp  = [intergenic_regions[j]]

                            new_nodes[  i].grays = new_nodes[  i].wcs = node_i.ap.ac.ap.wc[j]
                            new_nodes[i+1].grays = new_nodes[i+1].wcs = node_i.ap.ac.ap.wc[j]
                            new_nodes[  i].wc    = new_nodes[i+1].wc  = [node_i.ap.ac.ap.wc[j],]

                            new_nodes[  i].lc = len(new_nodes[  i].wc)-1
                            new_nodes[i+1].lc = len(new_nodes[i+1].wc)-1
                            new_nodes[  i].lp = len(new_nodes[  i].wp)-1
                            new_nodes[i+1].lp = len(new_nodes[i+1].wp)-1

                            j += 1

                        # create white edges between new edges
                        for i in range(0,number_of_new_nodes-1,2) :
                            new_nodes[  i].ab = new_nodes[i+1]
                            new_nodes[i+1].ab = new_nodes[  i]

                        # link new edges in the extremities with the old ones
                        node_left_left   = node_i.ap.ac        # +a
                        node_left_right  = node_left_left.ap   # -b
                        node_right_left  = node_i              # +c
                        node_right_right = node_i.ap           # -d
                        new_first        = new_nodes[0]        # -e
                        new_last         = new_nodes[-1]       # +e

                        gray_weights_helper = [node_left_right.wc[0], node_left_right.wc[-1]]

                        # trivial cycle, black and gray edges
                        new_last.ap        = new_last.ac        = node_left_right
                        node_left_right.ac = node_left_right.ap = new_last
                        # trivial cycle, black edges weights
                        new_last.blacks        = new_last.wps        = intergenic_regions[-1]
                        node_left_right.blacks = node_left_right.wps = intergenic_regions[-1]
                        new_last.wp            = node_left_right.wp  = [intergenic_regions[-1],]
                        # trivial cycle, gray edges weights
                        new_last.grays        = new_last.wcs        = gray_weights_helper[1]
                        node_left_right.grays = node_left_right.wcs = gray_weights_helper[1]
                        new_last.wc           = node_left_right.wc  = [gray_weights_helper[1],]
                        # trivial cycle, label flags
                        new_last.lc        = len(new_last.wc)-1
                        node_left_right.lc = len(node_left_right.wc)-1
                        new_last.lp        = len(new_last.wp)-1
                        node_left_right.lp = len(node_left_right.wp)-1

                        # non-trivial cycle, black and gray edges
                        new_first.ap        = node_left_left
                        node_left_left.ap   = new_first
                        new_first.ac        = node_right_left
                        node_right_left.ac = new_first
                        # non-trivial cycle, black edges weights
                        new_first.wp = node_left_left.wp = intergenic_regions[0]
                        if len(new_nodes[-1].wp) > 1 :
                            new_first.wps = node_left_left.wps = new_nodes[-1].wp[0] + new_nodes[-1].wp[-1]
                        else :
                            new_first.wps = node_left_left.wps = new_nodes[-1].wp[0]
                        new_first.blacks        =  node_left_left.blacks = new_first.wps + node_right_right.wps
                        node_right_right.blacks = node_right_left.blacks = new_first.wps + node_right_right.wps
                        # non-trivial cycles, gray edges weights
                        new_first.grays        = new_first.wcs        = gray_weights_helper[0]
                        node_right_left.grays = node_right_left.wcs = gray_weights_helper[0]
                        new_first.wc           = node_right_left.wc  = [gray_weights_helper[0],]
                        # non-trivial cycle, label flags
                        new_first.lc        = len(new_first.wc)-1
                        node_left_left.lc   = len(node_left_left.wc)-1
                        node_right_right.lc = len(node_right_right.wc)-1
                        node_right_left.lc  = len(node_right_left.wc)-1
                        new_first.lp        = len(new_first.wp)-1
                        node_left_left.lp   = len(node_left_left.wp)-1
                        node_right_right.lp = len(node_right_right.wp)-1
                        node_right_left.lp  = len(node_right_left.wp)-1

                        self.set_values()

        else : #we have a deletion
            tam_ir_removed = len(intergenic_regions)
            tam_ir_now = len(node_i.wp) - position_x

            if (tam_ir_removed > tam_ir_now) :
                print("ERRO: Delecao de mais blocos de regioes intergenicas que a regiao possui: (wp = %s: del = %s: start_pos_index = %s)" % (
                    str(node_i.wp),
                    str(intergenic_regions),
                    str(position_x)
                ) )
                sys.exit()

            if (intergenic_regions[1+position_x:-1] != node_i.wp[1+position_x:tam_ir_removed-1]) :
                print("ERRO: Delecao de regioes intermediarias nao consistentes com o existente: (wp = %s: del = %s: start_pos_index = %s)" % (
                    str(node_i.wp),
                    str(intergenic_regions),
                    str(position_x)
                ) )
                sys.exit()

            if tam_ir_removed > 1 :
                final_wp = node_i.wp[:position_x] + [ int(node_i.wp[position_x] - intergenic_regions[0] + node_i.wp[position_x + tam_ir_removed - 1] - intergenic_regions[-1]),] + node_i.wp[position_x + tam_ir_removed:]
                node_i.wp = node_i.ap.wp = final_wp
                if len(node_i.wp) > 1 :
                    node_i.wps = node_i.ap.wps = node_i.wp[0] + node_i.wp[-1]
                else :
                    node_i.wps = node_i.ap.wps = node_i.wp[0]
                node_i.lp = len(node_i.wp)-1
                node_i.ap.lp = len(node_i.ap.wp)-1
            else :
                final_wp = node_i.wp[:position_x] + [int(node_i.wp[position_x] - intergenic_regions[position_x]),] + node_i.wp[position_x + tam_ir_removed:]
                node_i.wp = node_i.ap.wp = final_wp

            if (node_i.wp[position_x] < 0) :
                print("ERRO: A região intergenica resultante na posicao afetada ficou com peso negativo: (wp = %s: del = %s: start_pos_index = %s)" % (
                    str(node_i.wp),
                    str(intergenic_regions),
                    str(position_x)
                ) )
                sys.exit()

        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.__num_balanced_cycles  = False                
        self.reset_indices()
        return unp_i

    ############################################################                
    ################### Auxiliary Methods  #####################
    ############################################################                
    def print_indices(self) :
        node = self.begin_node

        while node :
            print("%i, padded = %s" % (node.index, node.padded))
            node = node.ap
            print("%i, padded = %s" % (node.index, node.padded))
            node = node.ab

    def to_string(self) :
        self.clean_visit()        

        node = self.end_node        

        str_cycles = "("

        while node :
            if not node.visit :
                cycle_node = node
                cycle      = "("

                while not cycle_node.visit :
                    wc = cycle_node.wc
                    wp = cycle_node.wp
                    lc = cycle_node.lc
                    lp = cycle_node.lp
                    if cycle_node.index % 2 == 0 :
                        cycle = cycle + "%i<%s,%s>," % (-(cycle_node.index+2)/2,str(wp),str(wc))
                    else :
                        cycle = cycle + "%i<%s,%s>," % (+(cycle_node.index+1)/2,str(wp),str(wc))


                    cycle_node.visit = True
                    cycle_node = cycle_node.ap
                    cycle_node.visit  = True
                    cycle_node = cycle_node.ac
                    
                cycle = cycle[:-1] + "),"
                str_cycles = str_cycles + cycle
            node = node.ap.ab
        str_cycles = str_cycles[:-1] + ")"
        return str_cycles

            

    def get_cycles(self, want_vertices = False) :
        self.clean_visit()        

        node = self.end_node        
        cycles    = []
        vertices  = []

        while node :
            if not node.visit :
                cycle_node  = node
                cycle       = []
                cycle_nodes = []

                while not cycle_node.visit :
                    if cycle_node.index % 2 == 0 :
                        cycle.append( -(cycle_node.index+2)/2 )
                    else :
                        cycle.append( +(cycle_node.index+1)/2 )


                    cycle_node.visit = True
                    cycle_nodes.append(cycle_node)
                    cycle_node = cycle_node.ap
                    cycle_node.visit  = True
                    cycle_nodes.append(cycle_node)
                    cycle_node = cycle_node.ac
                    
                cycles.append(tuple(cycle))
                vertices.append(cycle_nodes)

            node = node.ap.ab
        if want_vertices :
            return tuple(cycles), vertices
        return tuple(cycles)


    def permutation(self) :
        self.set_values()
        permutation = ""
        node = self.begin_node 
        while node :
            if type(node.value) == bool :
                return ""
            node = node.ap
            if type(node.value) == bool :
                return ""
            node = node.ab

            if not type(node) == int :
                permutation += "%i," % node.value
        return permutation[:-1]

    ## Here we try to give values to the nodes to check if they are a
    ## permutation.
    def set_values(self) :
        node = self.begin_node        

        node.value = 0
        node = node.ac
        node.value = -1

        while node.ab :
            node = node.ab
            node.value = -(node.ab.value)
            node = node.ac

            if node.ac.value > 0 :
                node.value = -(node.ac.value + 1)
            else :
                node.value = -(node.ac.value - 1)
    
    def reset_indices(self) :
        node  = self.begin_node 
        count = 0

        while node :
            node.index = count

            node.lp    = len(node.wp)-1
            node.lc    = len(node.wc)-1

            node       = node.ap
            count      = count + 1
            
            node.index = count

            node.lp    = len(node.wp)-1
            node.lc    = len(node.wc)-1

            node       = node.ab
            count      = count + 1

    def num_cycles(self) :
        if type(self.__num_cycles) == bool :
            self.calculate_cycles()
        return self.__num_cycles

    def num_odd_cycles(self) :
        if type(self.__num_odd_cycles) == bool :
            self.calculate_cycles()
        return self.__num_odd_cycles


    def calculate_cycles(self) :
        cycles, vertices = self.get_cycles(want_vertices = True)
        num_cycles = len(cycles)
        num_odd = 0
        is_labeled = False

        for cycle in cycles :
            if len(cycle) % 2 == 1 :
                num_odd = num_odd + 1

        self.__num_cycles           = num_cycles
        self.__num_odd_cycles       = num_odd

        for i in range(len(cycles)) :            
            cycle = cycles[i]
            size = len(cycle)

            direction = 1
            for el in cycle :
                if (el < 0) :
                    direction = 2
                    break

            blacks   = 0
            grays    = 0
            vertice_set = vertices[i]
            is_gray_labeled = False
            is_black_labeled = False
            for vertex in vertice_set :
                if len(vertex.wc) == 1 :
                    vertex.lc = 0
                    vertex.wcs = vertex.wc[0]
                    grays   = grays   + vertex.wcs
                else :
                    vertex.lc = len(vertex.wc) - 1
                    vertex.wcs = vertex.wc[0] + vertex.wc[-1]
                    is_gray_labeled = True
                    grays   = grays   + vertex.wcs
                if len(vertex.wp) == 1 :
                    vertex.lp = 0
                    vertex.wps = vertex.wp[0]
                    blacks  = blacks  + vertex.wps
                else :
                    vertex.lp = len(vertex.wp) - 1
                    vertex.wps = vertex.wp[0] + vertex.wp[-1]
                    is_black_labeled = True
                    blacks  = blacks  + vertex.wps
            grays  = grays  // 2
            blacks = blacks // 2

            for vertex in vertice_set :
                vertex.size      = size
                vertex.grays     = grays
                vertex.blacks    = blacks
                vertex.direction = direction                
                #vertex.kind  = kind
                vertex.cycle = i
                vertex.gray_labeled = is_gray_labeled
                vertex.black_labeled = is_black_labeled

    def clean_visit(self) :
        node = self.begin_node
        
        while node :
            node.visit = False
            node       = node.ap
            node.visit = False
            node       = node.ab



############################################################################
############### Do not need to sort a real permutation #####################
############################################################################

## This class was developed to sort cycle-graph configurations. We
## apply several rules in order to make the configuration closer to
## the identity. If no rule is found, so the program returns with no
## error message. 

## If the input cycle configuration is a full component, then we
## guarantee that the final permutation is the identity.

class Intergenic_Rev :
    def __init__(self, cycles, wgray, wblack, final_length) :
        self.input_cycles  = str(cycles).replace(" ", "")
        self.input_wgray   = str(wgray).replace(" ", "")[1:-1]
        self.input_wblack  = str(wblack).replace(" ", "")[1:-1]
                        
        self.graph      = cycle_configuration_graph(cycles,
                                                    wgray,
                                                    wblack,
                                                    final_length)
        self.randomized = False

    def get_num_balanced(self, vertices) :
        num_balanced = 0
        for vertice in vertices :
            if vertice[0].grays == vertice[0].blacks :
                num_balanced = num_balanced + 1
        return num_balanced

    def get_num_clean_balanced(self, vertices) :
        num_balanced = 0
        for vertice in vertices :
            if vertice[0].grays == vertice[0].blacks and vertice[0].black_labeled == False and vertice[0].gray_labeled == False:
                num_balanced = num_balanced + 1
        return num_balanced
    
    def sort(self, start_time, allowed_ops) :
        sequence = []
        graph = self.graph

        graph.calculate_cycles()
        _, vertices = graph.get_cycles(want_vertices = True)
        num_balanced = self.get_num_clean_balanced(vertices)
        if DEBUG :
            print("NUM BALANCED --> %s" % num_balanced)
        if allowed_ops == 'R' :
            max_approx = 2.5
            lowerb = float( graph.n - num_balanced )
        elif allowed_ops == 'T' :
            max_approx = 4.0
            lowerb = float( graph.n - num_balanced )/2.0
        else : # ops == 'RT'
            max_approx = 4.0
            lowerb = float( graph.n - num_balanced )/2.0
        while True :
            if DEBUG :
                print(graph.get_cycles())
                print(graph.to_string())
                graph.calculate_cycles()
                permaux = eval("[%s]" % graph.permutation())
                permauxneg = sum(1 for nneg in permaux if nneg < 0)

                #_, vertices = graph.get_cycles(want_vertices = True)
                #num_balanced = 0
                #for vertice in vertices :
                #    print "black = %d gray = %d" % (vertice[0].blacks, vertice[0].grays)
                #    if vertice[0].grays == vertice[0].blacks :
                #        num_balanced = num_balanced + 1

            if allowed_ops == 'R' :
                operations = self.search_rev_indel(graph)
            elif allowed_ops == 'T' :
                operations = self.search_transp_indel(graph)
            else :
                operations = self.search_revtrans_indel(graph)

            if DEBUG :
                print(sequence)
                print(graph.to_string())

            if not operations :
                break

            if DEBUG :
                print("##############################")
                print(graph.to_string())            
            for op in operations :
                if callable(op[0]) :
                    graph.calculate_cycles()
                    if DEBUG :
                        print("calling : ", op[1].index, op[2].index, op[3].index)
                    append = op[0](*tuple(op[1:]))
                    for el in append :
                        operations.append(el)
                else :
                    op = self.format_node_to_operations_indel(op)
                    if DEBUG :
                        print("OPERACAO", op)
                    if op[0] == 0 :
                        graph.indel(op[0], op[1],op[2],op[3][0], op[3][1])
                        sequence.append(tuple(['DEL', op[1], op[2], op[3][0][:], op[3][1][:]]))
                    if op[0] == 1 :
                        graph.indel(op[0], op[1],op[2],op[3][0], op[3][1])
                        sequence.append(tuple(['INS', op[1], op[2], op[3][0][:], op[3][1][:]]))
                    if op[0] == 2 :
                        graph.reversal2(op[1],op[2],op[3][0], op[3][1], op[3][2], op[3][3])
                        sequence.append(tuple(['REV',op[1],op[2],op[3][0],op[3][1]]))
                    if op[0] == 3 :
                        graph.transposition2(op[1],op[2], op[3], op[4][0], op[4][1], op[4][2])
                        sequence.append(tuple(['TRANSP',op[1],op[2],op[3],[op[4][0][0],op[4][1][0],op[4][2][0]]]))
                    if DEBUG :
                        print(graph.to_string())
                    #print(op)
                    #print(graph.to_string())
                        
            ##################################################                    
            # Abaixo apenas depuracao        
            ##################################################
            graph.calculate_cycles()
            _, vertices = graph.get_cycles(want_vertices = True)
            num_balanced = self.get_num_balanced(vertices)
            #print(num_balanced)
            #if len(operations) > 1 :
            #    print("depois...",graph.to_string())
            if DEBUG :
                print("NUM BALANCED -->%s \n" % num_balanced)
            #sys.exit()
            
            
        graph.calculate_cycles()
        _, vertices = graph.get_cycles(want_vertices = True)
        num_balanced = 0
        for vertice in vertices :
            if vertice[0].grays == vertice[0].blacks :
                num_balanced = num_balanced + 1

        if num_balanced == graph.final_n :
            if (((1.0*len(sequence))/lowerb) <= max_approx) :
                print('%s [%s] [%s] %d %s %f %f' % (self.input_cycles,
                               self.input_wgray,
                               self.input_wblack,
                               len(sequence),
                               str(sequence).replace(" ", ""),
                               len(sequence)/lowerb,
                               float(time.time() - start_time)))
            else :
                print('%s [%s] [%s] %d %s %f %f ERROR-LOWER-BOUND-HIGHER' % (self.input_cycles,
                               self.input_wgray,
                               self.input_wblack,
                               len(sequence),
                               str(sequence).replace(" ", ""),
                               len(sequence)/lowerb,
                               time.time() - start_time))
        else :
            print('%s [%s] [%s] %d %s %f %f ERROR-NOT-SORTED' % (self.input_cycles,
                               self.input_wgray,
                               self.input_wblack,
                               len(sequence),
                               str(sequence).replace(" ", ""),
                               len(sequence)/lowerb,
                               time.time() - start_time))
     

    def format_node_to_operations_indel(self,operation) :
        if operation :
            if operation[0] == 3 : #transp
                i = int(round(float(operation[1].index + 1) / 2))
                j = int(round(float(operation[2].index + 1) / 2))
                k = int(round(float(operation[3].index + 1) / 2))
                return (3, i, j, k, operation[4])
            elif operation[0] == 2 : #rev
                #i = int(round(float(operation[1].index + 1) / 2))
                #j = int(round(float(operation[2].index + 1) / 2))
                i = int(math.ceil(float(operation[1].index + 1) / 2))
                j = int(math.ceil(float(operation[2].index + 1) / 2))
                return(2, i, j-1, operation[3])
            else : #indel
                #i = int(round(float(operation[1].index + 1) / 2))
                i = int(math.ceil(float(operation[1].index + 1) / 2))
                return(operation[0], i, operation[2], operation[3])


    ## Para reversões com indels
    def search_rev_indel(self, graph) :
        graph.calculate_cycles()
        operations = None
        
        if not operations :
            ## We will transform a trivial cycle C that is not black-labeled
            ## and it is either clean and unbalanced or gray-labeled and
            ## positive into a clean and balanced cycle
            operations = self.lemma_5(graph)
            if operations :
                return [operations]

        if not operations :
            ## We will transform a trivial cycle C that does not fit into
            ## lemma 5 (i.e., it is black-labeled or it is gray-labeled 
            ## and negative) into a clean and balanced cycle
            operations = self.lemma_6(graph)
            if operations :
                return [operations]

        if not operations :
            ## We will break a non-trivial cycle C that is divergent
            ## and not clean.
            operations = self.lemma_7(graph)
            if operations :
                return [operations]

        if not operations :
            ## We will break a non-trivial cycle C that is divergent
            ## and clean.
            operations = self.lemma_8(graph)
            if operations :
                return [operations]

        if not operations :
            ## At this step no divergent cycle exists. We will apply 
            ## a reversal to an oriented cycle that creates a new 
            ## divergent cycle.
            operations = self.lemma_9(graph)
            if operations :
                return [operations]

        if not operations :
            ## At this step no divergent cycle exists. We will apply 
            ## a reversal to any non trivial cycle that creates a new 
            ## divergent cycle.
            operations = self.lemma_10(graph)
            if operations :
                return [operations]


    def search_transp_indel(self, graph) :
        graph.calculate_cycles()
        operations = None

        if not operations :
            ## trivial bad cycle such that C is either clean or non-negative
            ## apply one indel
            operations = self.lemma_6_transp(graph)
            if operations :
                #print("lemma6 ", operations)
                return [operations]

        if not operations :
            ## trivial bad cycle, C is neg or the source edge is labeled
            ## one indel here, and one from lemma_6 in the next iteration
            operations = self.lemma_7_transp(graph)
            if operations :
                #print("lemma7 ", operations)
                return [operations]

        if not operations :
            ## good oriented cycle. with up to three transpositions
            ## we increase the number of good cycle by 2
            operations = self.lemma_3_transp(graph)
            if operations :
                #print("lemma3 ", operations)
                return operations

        if not operations :
            ## positive clean cycle. one insertion transforms into good
            operations = self.lemma_8_transp(graph)
            if operations :
                #print("lemma8 ", operations)
                return [operations]

        if not operations :
            ## oriented bad cycle, then a transp transforms C into three
            ## cycles such that one is a trivial non-negative cycle with
            ## a clean source edge
            operations = self.lemma_9_transp(graph)
            if operations :
                #print("lemma9 ", operations)
                return [operations]

        if not operations :
            ## at least two non-trivial bad cycles that are non-oriented,
            ## then one transposition transforms one of them into a trivial
            ## non-negative cycle with a clean source edge
            operations = self.lemma_10_transp(graph)
            if operations :
                #print("lemma10 ", operations)
                return [operations]

        if not operations :
            ## only one bad short cycle, any other cycle is good, and all
            ## cycles are non-oriented. first we apply an indel that transforms
            ## C into good. apply insertion to clean the target/gray edges,
            ## such that the leftmost is always a good cycle. after that, apply
            ## a deletion to each of the two labeled source edges to turn those
            ## cycles into good
            operations = self.lemma_11_transp(graph)
            if operations :
                #print("lemma11 ", operations)
                return operations

        if not operations :
            ## only one bad cycle that is long any other cycle is good, and all
            ## cycles are non-oriented. apply a transposition to the interleaving
            ## cycle that is good by definition, such that C is now oriented so
            ## we can apply lemma 9 / lemma 6 / lemma 3
            operations = self.lemma_12_transp(graph)
            if operations :
                #print("lemma12 ", operations)
                return [operations]

        if not operations :
            ## one good non-oriented long cycle and no oriented cycles in G(\pi)
            ## we apply one transposition here followed by lemma 3 twice, a total
            ## of 3-7 transpositions
            operations = self.lemma_4_transp(graph)
            if operations :
                #print("lemma4 ", operations)
                return [operations]

        if not operations :
            ## G(\pi) has only trivial and short cycles, and all are good, then
            ## one transp will transform two short cycles into a trivial good
            ## cycle and an oriented good cycle, so we can apply lemma 3
            # to increase the number of good cycles by 2
            operations = self.lemma_5_transp(graph)
            if operations :
                #print("lemma5 ", operations)
                return [operations]


    def search_revtrans_indel(self, graph) :
        graph.calculate_cycles()
        operations = None

        if not operations :
            ## trivial bad cycle such that C is either clean or non-negative
            ## apply one indel
            operations = self.lemma_5(graph)
            if operations :
                return [operations]

        if not operations :
            ## trivial bad cycle, C is neg or the source edge is labeled
            ## one indel here, and one from lemma_6 in the next iteration
            operations = self.lemma_6(graph)
            if operations :
                return [operations]

        if not operations :
            ## We will break a non-trivial cycle C that is divergent
            ## and not clean.
            operations = self.lemma_7(graph)
            if operations :
                return [operations]

        if not operations :
            ## We will break a non-trivial cycle C that is divergent
            ## and clean.
            operations = self.lemma_8(graph)
            if operations :
                return [operations]

        if not operations :
            ## good oriented cycle. with up to three transpositions
            ## we increase the number of good cycle by 2
            operations = self.lemma_3_transp(graph)
            if operations :
                return operations

        if not operations :
            ## positive clean cycle. one insertion transforms into good
            operations = self.lemma_8_transp(graph)
            if operations :
                return [operations]

        if not operations :
            ## oriented bad cycle, then a transp transforms C into three
            ## cycles such that one is a trivial non-negative cycle with
            ## a clean source edge
            operations = self.lemma_9_transp(graph)
            if operations :
                return [operations]

        if not operations :
            ## at least two non-trivial bad cycles that are non-oriented,
            ## then one transposition transforms one of them into a trivial
            ## non-negative cycle with a clean source edge
            operations = self.lemma_10_transp(graph)
            if operations :
                return [operations]

        if not operations :
            ## only one bad short cycle, any other cycle is good, and all
            ## cycles are non-oriented. first we apply an indel that transforms
            ## C into good. apply insertion to clean the target/gray edges,
            ## such that the leftmost is always a good cycle. after that, apply
            ## a deletion to each of the two labeled source edges to turn those
            ## cycles into good
            operations = self.lemma_11_transp(graph)
            if operations :
                return operations

        if not operations :
            ## only one bad cycle that is long any other cycle is good, and all
            ## cycles are non-oriented. apply a transposition to the interleaving
            ## cycle that is good by definition, such that C is now oriented so
            ## we can apply lemma 9 / lemma 6 / lemma 3
            operations = self.lemma_12_transp(graph)
            if operations :
                return [operations]

        if not operations :
            ## one good non-oriented long cycle and no oriented cycles in G(\pi)
            ## we apply one transposition here followed by lemma 3 twice, a total
            ## of 3-7 transpositions
            operations = self.lemma_4_transp(graph)
            if operations :
                return [operations]

        if not operations :
            ## G(\pi) has only trivial and short cycles, and all are good, then
            ## one transp will transform two short cycles into a trivial good
            ## cycle and an oriented good cycle, so we can apply lemma 3
            # to increase the number of good cycles by 2
            operations = self.lemma_5_transp(graph)
            if operations :
                return [operations]


##################################################
############### Several Steps ####################
##################################################


    ## Receive two nodes in the same cycle.
    def __check_convergency(self, graph, v_i, v_j) :
        if v_i.cycle == v_j.cycle :
            
            node = v_i.ap.ac 
            while node.index != v_i.index :
                node = node.ap.ac 
                if node.index == v_j.index :                    
                    return True
            return False
        print ("Error: Edges in different cycles")
        sys.exit()


    ## Search crossing edges. The point of this method is to find a
    ## reversal that transforms two black edges that are convergent
    ## into two black edges that are divergent. I will usually put
    ## these two black edges as parameters.
    def __search_crossing_edges(self, graph, v_i, v_j, any_cycle = False) :
        ## b is the rightmost and in the right side of the black edge
        a,b = v_i, v_j
        if a.index > b.index :
            a,b = b,a
        if a.index % 2 == 0 :
            a = a.ap
        if b.index % 2 == 0 :
            b = b.ap

        half1 = {}
        half2 = {}
        
        ## starting the search
        node = graph.end_node
        while node != b :
            half1[node.cycle] = node
            node = node.ap.ab
                    
        node = b.ap.ab
        while node != a :
            half2[node.cycle] = node
            node = node.ap.ab
        
        node = a.ap.ab
        while node :
            half1[node.cycle] = node
            node = node.ap.ab

        for key in list(half1.keys()) :
            if key in half2 :
                a,b = half1[key], half2[key]
                if ( key != v_i.cycle or
                     self.__check_convergency(graph, a, b) ) :
                    if a.index > b.index :
                        a,b = b,a
                    return a,b

    ## This is an auxiliary method called in the next method for
    ## simplicity. Remember we are talking about reversals. In order
    ## to understand this method, we advise you to draw the four cases
    ## in a piece of paper and try to code.
    def __indel_compute_balance(self, v_i, v_j, balance, available, go_right):
        ## Check if the first cycle can be
        ## balanced. Keep in mind that balance
        ## refers to the cycle that will have v_i.
        if (0 <= balance <= available) :
            a, b = v_j, v_i
            if (v_i.index < v_j.index) :
                a,b = v_i, v_j
            exchange = balance - a.wp[0]
            
            if go_right : ## We need balance in
                          ## the right                                    
                return (a,b, balance - b.wp[0]) 
            else : ## We need balance in the left
                return (a, b, a.wp[0] - balance) 

    ## This should be applied on black edges v_i and v_j in the same
    ## cycle. The inputs partial_gray and partial_black represents the
    ## gray and black edges that goes from v_i to v_j starting from a
    ## gray edge. In this case, it is going to be the gray edges in a
    ## cycle that would be formed if the reversal was applied
    def __indel_get_balance(self, v_i, v_j, partial_gray, partial_black) :
                        
        ## E necessario desenhar os casos no papel para entender a
        ## linha abaixo.
        v_i_right     = (v_i.index > v_i.ap.index)
        balance      = partial_gray - partial_black

        grays  = v_i.grays  ## Sum of gray  edges
        blacks = v_i.blacks ## Sum of black edges

        available=v_i.wp[0] + v_j.wp[0] ## Amount of
                                  ## weight that
                                  ## can go to any
                                  ## cycle.
        #print("aa",v_i.index, v_j.index, available, balance,
        #      partial_gray, partial_black)


        go_right = v_i_right
        op = self.__indel_compute_balance(v_i, v_j, balance, available, go_right)
        if op :
            return op
        
        go_right     = not  v_i_right                            
        remain_gray  = grays  - partial_gray 
        remain_black = blacks - partial_black - available
        balance     = remain_gray - remain_black
        op = self.__indel_compute_balance(v_i, v_j, balance, available, go_right)
        if op :
            return op

    ## use this just for transpositions
    def __sum_weight_in_segment(self, init, end) :
        node = init
        blacks = 0
        grays  = 0
        while node.index != end.index :
            blacks += node.wp[0]
            if len(node.wp) > 1 :
                blacks += node.wp[-1]
            node   = node.ap
            grays += node.wc[0]
            if len(node.wc) > 1 :
                grays += node.wc[-1]
            node   = node.ac
        return blacks, grays


    def compute_score(self, gray_ws, black_ws, ws, i, wi) :
        ws[i][0] = wi ## Inicio da cadeia.
        ws[i][1] = black_ws[i] - wi ## Restrição forte
        ws[(i+1)%3][1] = gray_ws[i] - wi ## Restrição fraca.
        ws[(i+1)%3][0] = black_ws[(i+1)%3] - ws[(i+1)%3][1]

        if (ws[i][0] < 0 or
            ws[i][1] < 0 or
            ws[(i+1)%3][0] < 0  or
            ws[(i+1)%3][1] < 0) :
            return -1
        ## Ja colocamos todos os pesos que tinham
        ## alguma restricao. Agora temos uma
        ## aresta preta que devemos otimizar.
        best_weight, best_score = -1, 100000000000000
        for last_weight in range(0, int(black_ws[(i+2)%3]+1)) :
            complementar = black_ws[(i+2)%3] - last_weight
            ws[(i+2)%3][0] = last_weight
            ws[(i+2)%3][1] = complementar
            score = (abs(gray_ws[(i+1)%3] - (ws[(i+1)%3][0] + ws[(i+2)%3][1])) +
                     abs(gray_ws[(i+2)%3] - (ws[(i+2)%3][0] + ws[(i+3)%3][1])))
            if last_weight >= 0 and complementar >= 0 :
                if score < best_score :
                    best_weight = last_weight
                    best_score  = score
        ws[(i+2)%3][0] = best_weight
        ws[(i+2)%3][1] = black_ws[(i+2)%3] - ws[(i+2)%3][0]
        return best_score



    def find_all_triples(self, cycle) :
        triples = []
        k = cycle[0]

        while True :  ## Loop over k
            i = k.ap.ac
            while True : ## Loop over i
                j = i.ap.ac                
                while True : ## Loop over j
                    if (k.index > j.index > i.index) :
                        triples.append([i, j, k] )
                    j = j.ap.ac
                    if j.index == k.index :
                        break
                i = i.ap.ac
                if i.ap.ac.index == k.index :
                    break            
            k = k.ap.ac
            if k.index == cycle[0].index :
                break
            
        #for triple in triples :
        #    print("Triples: ", triple[0].index, triple[1].index, triple[2].index)        
        return(triples)

    def find_all_triples_two_adj(self, cycle) :
        triples = []
        k = cycle[0]

        while True :  ## Loop over k
            i = k.ap.ac
            while True : ## Loop over i
                j = i.ap.ac                
                while True : ## Loop over j
                    if (
                          (k.index > j.index > i.index) and
                          (
                              i == k.ap.ac or
                              j == i.ap.ac or
                              k == j.ap.ac
                          )
                       ) :
                        triples.append([i, j, k] )
                    j = j.ap.ac
                    if j.index == k.index :
                        break
                i = i.ap.ac
                if i.ap.ac.index == k.index :
                    break            
            k = k.ap.ac
            if k.index == cycle[0].index :
                break
            
        #for triple in triples :
        #    print("Triples: ", triple[0].index, triple[1].index, triple[2].index)        
        return(triples)

    ## First lemma, we will try to transform a trivial not black-labeled cycle
    ## that is (i) not balanced or (ii) gray-labeled and non-negative into a 
    ## balanced clean cycle using one indel
    def lemma_5(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if cycle[0].size == 1 and cycle[0].black_labeled == False and (
                 (cycle[0].gray_labeled == False and cycle[0].blacks != cycle[0].grays) or
                 (cycle[0].gray_labeled == True  and cycle[0].blacks <= cycle[0].grays)
            ) :
                if cycle[0].gray_labeled == False : ## we just modify the weight of the black edge
                    indel_position = 0
                    indel_sequence = [int(cycle[0].wc[0] - cycle[0].wp[0]),]
                    operation = 1
                    pi_inserted = []
                    if indel_sequence[0] < 0 :
                        operation = 0
                        indel_sequence[0] = -indel_sequence[0]
                else : ## we must add some new elements
                    operation = 1
                    pi_inserted = cycle[0].lc_iota
                    if ((cycle[0].index > cycle[0].ap.index and cycle[0].value > 0) or
                       (cycle[0].index < cycle[0].ap.index and cycle[0].value < 0)) :
                        pi_inserted = [-i for i in pi_inserted[::-1]]
                        cycle[0].wc = cycle[0].ap.wc = cycle[0].wc[::-1]
                    if (cycle[0].wc[0] >= cycle[0].wp[0]) :
                        indel_position = cycle[0].wp[0]
                        indel_sequence = [int(cycle[0].wc[0] - cycle[0].wp[0]),] + cycle[0].wc[1:]
                    else :
                        indel_position = cycle[0].wc[0]
                        indel_sequence = [0, ] + cycle[0].wc[1:]
                        indel_sequence[-1] = max(0,int(indel_sequence[-1] - (cycle[0].wp[0] - cycle[0].wc[0])))
                return (operation, cycle[0], indel_position, [pi_inserted, indel_sequence])
        return None

    ## Second lemma, we will try to transform a trivial black-labeled cycle
    ## into a trivial not black-labeled cycle, and eventually apply lemma_5
    def lemma_6(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].size == 1) and (cycle[0].black_labeled or cycle[0].blacks > cycle[0].grays) :
                if cycle[0].black_labeled : #we will remove some alphas
                    if (cycle[0].wp[0] >= cycle[0].grays) :
                        indel_position = cycle[0].grays
                        indel_sequence = [int(cycle[0].wp[0] - cycle[0].grays),] + cycle[0].wp[1:]
                    elif (cycle[0].wp[-1] >= cycle[0].grays) :
                        indel_position = 0
                        indel_sequence = cycle[0].wp[:-1] + [int(cycle[0].wp[-1] - cycle[0].grays),]
                    elif (cycle[0].wp[0] + cycle[0].wp[-1] >= cycle[0].grays) :
                        indel_position = cycle[0].wp[0]
                        indel_sequence = [0,] + cycle[0].wp[1:-1] + [int(cycle[0].wp[-1]+cycle[0].wp[0]-cycle[0].grays),]
                    else : #lemma_5 will be applied after this...
                        indel_position = cycle[0].wp[0]
                        indel_sequence = [0,] + cycle[0].wp[1:-1] + [0,]
                else : # we will just remove an intergenic size
                    indel_position = 0
                    indel_sequence = [cycle[0].blacks - cycle[0].grays]
                return (0, cycle[0], indel_position, [[0 for _ in range(0,cycle[0].lp)], indel_sequence])
        return None

    ## Third lemma, we will try to transform a divergent cycle C into one trivial
    ## not black-labeled cycle and one cycle with the remaining edges
    ## after this lemma, we may apply lemma 5 in the trivial one.
    def lemma_7(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].direction == 2) and (cycle[0].gray_labeled == True or cycle[0].black_labeled == True) :
                start_point = cycle[0]
                a = cycle[0]
                b = a.ap.ac
                trivial, other = None, None
                if (a.index%2 != b.index%2) :
                    if a.index > a.ap.index :
                        if a.index < b.index :
                            trivial, other = a, b
                        else :
                            trivial, other = b, a
                    else :
                        if a.index < b.index :
                            trivial, other = b, a
                        else :
                            trivial, other = a, b
                    
                else :
                    a = a.ap.ac
                    b = b.ap.ac
                    while (a.index != start_point.index) and (trivial == None) :
                        if (a.index%2 != b.index%2) :
                            if a.index > a.ap.index :
                                if a.index < b.index :
                                    trivial, other = a, b
                                else :
                                    trivial, other = b, a
                            else :
                                if a.index < b.index :
                                    trivial, other = b, a
                                else :
                                    trivial, other = a, b
                        else :
                            a = a.ap.ac
                            b = b.ap.ac

                if trivial != None :
                    length_needed = trivial.wc[0]
                    if len(trivial.wc) > 1 :
                        length_needed += trivial.wc[-1]

                    if trivial.index < other.index : ## a trivial cycle will be created in the left
                        if (trivial.wp[0] + other.wp[0] >= length_needed) :
                            cut_left_ir = min(length_needed, trivial.wp[0])
                            cut_right_ir = length_needed - cut_left_ir
                            res_left_ir = [length_needed,]
                            res_right_ir = trivial.wp[1:][::-1] + [int(other.wp[0] + trivial.wp[0] - length_needed),] + other.wp[1:]
                        else :
                            cut_left_ir = trivial.wp[0]
                            cut_right_ir = other.wp[0]
                            res_left_ir = [int(trivial.wp[0] + other.wp[0]),]
                            res_right_ir = trivial.wp[1:][::-1] + [0,] + other.wp[1:]
                        return(2,trivial,other,[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
                    else : ## a trivial cycle will be created in the right)
                        if (trivial.wp[-1] + other.wp[-1] >= length_needed) :
                            already_in_the_right = min(length_needed, trivial.wp[-1])
                            cut_right_ir = sum(trivial.wp[:-1]) + trivial.wp[-1] - already_in_the_right
                            cut_left_ir =  sum(other.wp[:-1]) + (other.wp[-1] + trivial.wp[-1] - already_in_the_right)
                            res_left_ir = other.wp[:-1] + [int(trivial.wp[-1] + other.wp[-1] - length_needed),] + trivial.wp[:-1][::-1] 
                            res_right_ir = [length_needed,]
                        else :
                            cut_left_ir = sum(other.wp[:-1])
                            cut_right_ir = sum(trivial.wp[:-1])
                            res_left_ir =  other.wp[:-1] + [0,] + trivial.wp[:-1][::-1]
                            res_right_ir = [int(other.wp[-1]+trivial.wp[-1]),]
                        return(2,trivial,other,[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
        return None

    ## Fourth lemma, we will try to transform a divergent clean cycle C:
    ##  (  i) into a balanced cycle, if C is positive
    ##  ( ii) into two balanced cycles, if C is balanced
    ##  (iii) into one balanced cycle and one negative cycle otherwise
    def lemma_8(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].direction == 2) and (cycle[0].gray_labeled == False) and (cycle[0].black_labeled == False) :

                if (cycle[0].grays > cycle[0].blacks) : ## C is a positive cycle
                    indel_sequence = [int(cycle[0].grays - cycle[0].blacks),]
                    return(1,cycle[0], 0, [[], indel_sequence])
                else :  
                    for i in range(1, len(cycle) - 2, 2) :
                        v_i           = cycle[i]
                        
                        partial_gray  =  v_i.wc[0]
                        partial_black =  0
                        for j in range(i+2, len(cycle), 2)  :
                            v_j           = cycle[j]

                            if (v_i.index%2 != v_j.index%2): ## Check divergence
                                op = self.__indel_get_balance(v_i, v_j, partial_gray, partial_black)
                                if op :
                                    if op[2] >= 0 :
                                        cut_left_ir = op[0].wp[0] - op[2]
                                        cut_right_ir = 0
                                        res_left_ir = [cut_left_ir,]
                                        res_right_ir = [int(op[1].wp[0] + op[2]),]
                                    else :
                                        cut_left_ir = op[0].wp[0]
                                        cut_right_ir = -op[2]
                                        res_left_ir = [int(cut_left_ir - op[2]),]
                                        res_right_ir = [int(op[1].wp[0] + op[2]),]
                                    return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
                                
                            ## Preparing next iteration    
                            partial_gray  = partial_gray  + v_j.wc[0]
                            partial_black = partial_black + v_j.wp[0]
        return None

    def lemma_alcob(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
          if cycle[0].size > 1 :#and cycle[0].grays <= cycle[0].blacks :
            #print(str(cycle[0]),cycle[0].grays, cycle[0].blacks)
            for i in range(1, len(cycle) - 2, 2) :
                v_i           = cycle[i]
                partial_gray  =  v_i.wc[0]
                partial_black =  0
                for j in range(i+2, len(cycle), 2)  :
                    v_j           = cycle[j]
                    #op = self.__indel_get_balance(v_i, v_j, partial_gray, partial_black)
                    #if op :
                    op = self.__search_crossing_edges(graph, v_i, v_j)
                    if op :
                        cut_left_ir = sum(op[0].wp)
                        cut_right_ir = 0
                        res_left_ir = op[0].wp
                        res_right_ir = op[1].wp
                        return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
                            
                    ## Preparing next iteration    
                    partial_gray  = partial_gray  + v_j.wc[0]
                    partial_black = partial_black + v_j.wp[0]
        ##if there is no crossing cycles, all long cycles are oriented.
        for cycle in vertices :
          if cycle[0].size > 2 :#and cycle[0].grays <= cycle[0].blacks :
            triples = self.find_all_triples(cycle)
            if triples :
                op = [triples[0][1], triples[0][2]]
                cut_left_ir = sum(op[0].wp)
                cut_right_ir = 0
                res_left_ir = op[0].wp
                res_right_ir = op[1].wp
                return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])

        return None

    ## This lemma searches for an oriented convergent cycle, and will transform
    ## it into a divergent cycle
    def lemma_9(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
          if cycle[0].size > 2 :#and cycle[0].grays <= cycle[0].blacks :
            triples = self.find_all_triples(cycle)
            if triples :
                op = [triples[0][1], triples[0][2]]
                cut_left_ir = sum(op[0].wp)
                cut_right_ir = 0
                res_left_ir = op[0].wp
                res_right_ir = op[1].wp
                return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])

        return None        

    ## last step: there are only non-oriented convergent cycles
    def lemma_10(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
          if cycle[0].size > 1 :#and cycle[0].grays <= cycle[0].blacks :
            #print(str(cycle[0]),cycle[0].grays, cycle[0].blacks)
            for i in range(1, len(cycle) - 2, 2) :
                v_i           = cycle[i]
                partial_gray  =  v_i.wc[0]
                partial_black =  0
                for j in range(i+2, len(cycle), 2)  :
                    v_j           = cycle[j]
                    #op = self.__indel_get_balance(v_i, v_j, partial_gray, partial_black)
                    #if op :
                    op = self.__search_crossing_edges(graph, v_i, v_j)
                    if op :
                        cut_left_ir = sum(op[0].wp)
                        cut_right_ir = 0
                        res_left_ir = op[0].wp
                        res_right_ir = op[1].wp
                        return (2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
                            
                    ## Preparing next iteration    
                    partial_gray  = partial_gray  + v_j.wc[0]
                    partial_black = partial_black + v_j.wp[0]

        return None

    def lemma_3_transp(self, graph, hasMove = False) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].direction == 1 and ## Check if it is convergent
                cycle[0].size      >= 3 and ## Check if it is long
                cycle[0].gray_labeled == False and                 # not gray labeled,
                cycle[0].black_labeled == False and                 # not black labeled, and
                cycle[0].blacks    == cycle[0].grays ## Check if it is
                                                     ## breakable,
                                                     ## which means we
                                                     ## need more
                                                     ## weight in
                                                     ## black edges
                                                     ## than gray
                                                     ## edges
            ) :
                triples = self.find_all_triples(cycle)
                #for tr in triples:
                #    print tr[0].index, tr[1].index, tr[2].index
              
                for transp in triples :
                    ## Let us compute the segment weights between
                    ## the edges that will be broken. We will call
                    ## it gray_weights, even though it may not
                    ## represent weights
                    gray_weights = []
                    ## Pesos das arestas pretas
                    black_weights = []
                    ## Here I will place the transp weights. A
                    ## soma de cada bloco tem que dar o peso da
                    ## aresta preta correspondente.
                    transp_weights = [[0,0],[0,0],[0,0]] 

                    ## Computing the gray black weights.
                    for i in range(len(transp)) :
                        init, end = transp[i], transp[(i+1)%3]
                        blacks, grays = self.__sum_weight_in_segment(init, end)
                        blacks = blacks - init.wp[0]
                        # transp_weights[i][0] = init.wp[0]
                        black_weights.append(init.wp[0])
                        gray_weights.append(grays - blacks)
                    #print(transp[0].index, transp[1].index, transp[2].index)
                    #print(black_weights, gray_weights)

                    ## NÃ£o entendi o cÃ³digo anterior, vou criar um
                    ## que faz mais sentido.
                    
                    ## Passo 1: Devo escolher uma aresta preta com
                    ## peso maior que ou igual Ã  aresta cinza
                    ## (funÃ§Ã£o g(.) na verdade) incidente a ela
                    ## pela esquerda. Podemos provar que existe
                    ## pelo menos uma satisfazendo esse critÃ©rio
                    ## por contradiÃ§Ã£o.

                    # Trocando
                    # heaviest_black = None
                    # for i in range(3) :
                    #     if black_weights[i] >= gray_weights[i] :
                    #         heaviest_black = i
                    #         break

                    best_score  = 100000000000000
                    best_weight = 100000000000000
                    best_black  = -1
                    
                    #print("#############################################")
                    for heaviest_black in (0,1,2) :                            
                        #print("########################################", heaviest_black)
                        ## Passo 2: A aresta cinza Ã  esquerda de
                        ## heaviest_black deve garantir um ciclo
                        ## balanceado porque a aresta preta tem peso
                        ## para dar a ela. O que devemos fazer agora,
                        ## Ã© garantir que as duas outras arestas
                        ## pretas vÃ£o se aproximar do peso das suas
                        ## aresta cinzas. Para isso, vou criar um
                        ## score para uma atribuiÃ§Ã£o de pesos. Esse
                        ## score Ã© simplesmente a soma absoluta da
                        ## diferenÃ§a de pesos entre as arestas pretas
                        ## e cinzas na configuraÃ§Ã£o resultante.
    
                        #print(black_weights)    
                        #print("++++++++++++++++++++ HEAVIEST", heaviest_black)
    
                        for weight in range(0, int(black_weights[heaviest_black])+1) :
                            score = self.compute_score(gray_weights, black_weights,
                                                       transp_weights, heaviest_black,
                                                       weight)
                            #print("score = %s, weight = %s" % (score, weight))
                            #print(transp_weights) 
    
                            if score >= 0 and score < best_score :
                                #print("changing")
                                best_score  = score
                                best_weight = weight
                                best_black  = heaviest_black
                                                                            
                        #print("BEST ", best_weight, best_score)
                        #print(best_black)
                    if best_black != -1 and best_score == 0 :
                        self.compute_score(gray_weights, black_weights, transp_weights,
                                           best_black, best_weight)
                            
                        #print("-------> WEIGHTS: ", black_weights, gray_weights, transp_weights, best_score)
                        
                                    
                        outcome = [
                            gray_weights[0] - (transp_weights[0][0] + transp_weights[1][1]),
                            gray_weights[1] - (transp_weights[1][0] + transp_weights[2][1]),
                            gray_weights[2] - (transp_weights[2][0] + transp_weights[0][1])
                        ]
                        
                        end_point = 0
                        for el in outcome :
                            if el == 0:
                                end_point = end_point + 1
                        
                        start_point = int(cycle[0].blacks  == cycle[0].grays)
                        
                        #print(end_point, start_point)
                        #print(outcome)
                        #sys.exit()
                        
                        #if True :
                        if end_point - start_point > 0 :
                            return [(
                                3, transp[0], transp[1], transp[2],
                                [[transp_weights[0][0]+transp_weights[1][1]], [transp_weights[0][1]+transp_weights[2][0]], [transp_weights[1][0]+transp_weights[2][1]]]
                            )]#transp_weights[0][0], transp_weights[1][0], transp_weights[2][0])]
                        else :
                            return [
                               (3, transp[0], transp[1], transp[2],
                                #transp_weights[0][0], transp_weights[1][0], transp_weights[2][0]),
                                [[transp_weights[0][0]+transp_weights[1][1]], [transp_weights[0][1]+transp_weights[2][0]], [transp_weights[1][0]+transp_weights[2][1]]]),
                                #(self.__search_trivial_unbalanced_transposition, transp[0], transp[1], transp[2])]
                                (self.__make_sure_the_three_cycles_are_balanced, graph, transp[0], transp[1], transp[2])]

                for transp in triples :
                    ## Let us compute the segment weights between
                    ## the edges that will be broken. We will call
                    ## it gray_weights, even though it may not
                    ## represent weights
                    gray_weights = []
                    ## Pesos das arestas pretas
                    black_weights = []
                    ## Here I will place the transp weights. A
                    ## soma de cada bloco tem que dar o peso da
                    ## aresta preta correspondente.
                    transp_weights = [[0,0],[0,0],[0,0]] 

                    ## Computing the gray black weights.
                    for i in range(len(transp)) :
                        init, end = transp[i], transp[(i+1)%3]
                        blacks, grays = self.__sum_weight_in_segment(init, end)
                        blacks = blacks - init.wp[0]
                        # transp_weights[i][0] = init.wp[0]
                        black_weights.append(init.wp[0])
                        gray_weights.append(grays - blacks)
                    #print(transp[0].index, transp[1].index, transp[2].index)
                    #print(black_weights, gray_weights)

                    ## NÃ£o entendi o cÃ³digo anterior, vou criar um
                    ## que faz mais sentido.
                    
                    ## Passo 1: Devo escolher uma aresta preta com
                    ## peso maior que ou igual Ã  aresta cinza
                    ## (funÃ§Ã£o g(.) na verdade) incidente a ela
                    ## pela esquerda. Podemos provar que existe
                    ## pelo menos uma satisfazendo esse critÃ©rio
                    ## por contradiÃ§Ã£o.

                    # Trocando
                    # heaviest_black = None
                    # for i in range(3) :
                    #     if black_weights[i] >= gray_weights[i] :
                    #         heaviest_black = i
                    #         break

                    best_score  = 100000000000000
                    best_weight = 100000000000000
                    best_black  = -1
                    
                    #print("#############################################")
                    for heaviest_black in (0,1,2) :                            
                        #print("########################################", heaviest_black)
                        ## Passo 2: A aresta cinza Ã  esquerda de
                        ## heaviest_black deve garantir um ciclo
                        ## balanceado porque a aresta preta tem peso
                        ## para dar a ela. O que devemos fazer agora,
                        ## Ã© garantir que as duas outras arestas
                        ## pretas vÃ£o se aproximar do peso das suas
                        ## aresta cinzas. Para isso, vou criar um
                        ## score para uma atribuiÃ§Ã£o de pesos. Esse
                        ## score Ã© simplesmente a soma absoluta da
                        ## diferenÃ§a de pesos entre as arestas pretas
                        ## e cinzas na configuraÃ§Ã£o resultante.
    
                            
                        #print("++++++++++++++++++++ HEAVIEST", heaviest_black)
    
                        for weight in range(0, int(black_weights[heaviest_black])+1) :
                            score = self.compute_score(gray_weights, black_weights,
                                                       transp_weights, heaviest_black,
                                                       weight)
                            #print("score = %s, weight = %s" % (score, weight))
                            #print(transp_weights) 
    
                            if score >= 0 and score < best_score :
                                #print("changing")
                                best_score  = score
                                best_weight = weight
                                best_black  = heaviest_black
                                                                            
                        #print("BEST ", best_weight, best_score)
                        #print(best_black)
                    if best_black != -1 :
                        self.compute_score(gray_weights, black_weights, transp_weights,
                                           best_black, best_weight)
                            
                        #print("-------> WEIGHTS: ", black_weights, gray_weights, transp_weights, best_score)
                        
                                    
                        outcome = [
                            gray_weights[0] - (transp_weights[0][0] + transp_weights[1][1]),
                            gray_weights[1] - (transp_weights[1][0] + transp_weights[2][1]),
                            gray_weights[2] - (transp_weights[2][0] + transp_weights[0][1])
                        ]
                        
                        end_point = 0
                        for el in outcome :
                            if el == 0:
                                end_point = end_point + 1
                        
                        start_point = int(cycle[0].blacks  == cycle[0].grays)
                        
                        #print(end_point, start_point)
                        #print(outcome)
                        #sys.exit()
                        
                        #if True :
                        if end_point - start_point > 0 :
                            return [(
                                3, transp[0], transp[1], transp[2],
                                [[transp_weights[0][0]+transp_weights[1][1]], [transp_weights[0][1]+transp_weights[2][0]], [transp_weights[1][0]+transp_weights[2][1]]]
                            )] #transp_weights[0][0], transp_weights[1][0],transp_weights[2][0])

                        else :
                            return [
                               (3, transp[0], transp[1], transp[2],
                                #transp_weights[0][0], transp_weights[1][0], transp_weights[2][0]),
                                [[transp_weights[0][0]+transp_weights[1][1]], [transp_weights[0][1]+transp_weights[2][0]], [transp_weights[1][0]+transp_weights[2][1]]]),
                                #(self.__search_trivial_unbalanced_transposition, transp[0], transp[1], transp[2])]
                                (self.__make_sure_the_three_cycles_are_balanced, graph, transp[0], transp[1], transp[2])]
                            print("ERROR: " +  graph.to_string())



    ## Here I get a nonoriented cycle and I get edges in the open
    ## gates. As a second criterium, I select only the heaviest edges.
    def __search_interleaving_edges(self, graph, v_i, v_j, v_k) :
        ## c is the rightmost and in the right side of the black
        ## edge. I first put everybody in its place.
        a,b,c = v_i, v_j, v_k
        if a.index > b.index :
            a,b = b,a
        if b.index > c.index :
            b,c = c,b
        if a.index > b.index :
            a,b = b,a
            
        if a.index % 2 == 0 :
            a = a.ap
        if b.index % 2 == 0 :
            b = b.ap
        if c.index % 2 == 0 :
            c = b.ap
            
        ## Now I create the halves
            
        half0 = {} ## outside
        half1 = {}
        half2 = {}

        ## starting the search
        graph.clean_visit()
        node = graph.end_node
        while node != c :
            node.visit = 0
            if node.cycle in half0 and node.wp[0] < half0[node.cycle].wp[0] :
                pass
            else :
                half0[node.cycle] = node
            node = node.ap.ab
                
        ## starting the search
        node = c.ap.ab
        while node != b :
            node.visit = 1
            if node.cycle in half1 and node.wp[0] < half1[node.cycle].wp[0] :
                pass
            else :
                half1[node.cycle] = node
            node = node.ap.ab
                    
        node = b.ap.ab
        while node != a :
            node.visit = 2            
            if node.cycle in half2 and node.wp[0] < half2[node.cycle].wp[0] :
                pass
            else :
                half2[node.cycle] = node
            node = node.ap.ab
        
        node = a.ap.ab
        while node :
            node.visit = 0            
            if node.cycle in half0 and node.wp[0] < half0[node.cycle].wp[0] :
                pass
            else :                
                half0[node.cycle] = node
            node = node.ap.ab

        ## Let us first try interleave
        for key in list(half0.keys()) :
            if key in half1 and key in half2 :
                a,b,c = half0[key], half2[key], half1[key]
                if ( key != v_i.cycle ) :
                    if a.index > c.index :
                        return b, c, a
                    else :
                        return a, b, c

        ## Let us clean the dictionary, there might be many unitary
        ## cycles or cycles in only one half. We do not need them.
        for half in (half0, half1, half2) :
            for key in list(half.keys()) :
                num = 0
                if key in half0 :
                    num = num + 1
                if key in half1 :
                    num = num + 1
                if key in half2 :
                    num = num + 1
                ## It is in only one half. So we remove it
                if num == 1 :
                    half.pop(key, None)
                    
        ## Let us try shattered and balanced. A balanced is in only
        ## two blocks, so this loop could be improved, however I will
        ## let it as it is for now.
        for half in (half0, half1, half2) :
            for key in list(half.keys()) :
                if (key != v_i.cycle and half[key].grays == half[key].blacks) :
                    ## Now I need to find two edges in different regions
                    ## such that sum of black edges is bigger than the
                    ## balance in both sides.
                    keep_searching = True
                    found          = False
                    init = half[key]
                    end  = init.ap.ac
                    while keep_searching :
                        while end != init and keep_searching :
                            if end.visit != init.visit :
                                blacks, grays = self.__sum_weight_in_segment(init, end)
                                blacks = blacks - init.wp[0]
                                if 0 <= grays - blacks <= init.wp[0] + end.wp[0] :
                                    keep_searching = False
                                    found          = True
                                    break
                            end = end.ap.ac
                        if keep_searching :
                            init = init.ap.ac
                            if init == half[key] :
                                keep_searching = False
                                found          = False
        
                    if found :
                        a,b,c = init, end, None
                        visited = (init.visit, end.visit)
                        if 0 not in visited :
                            c = half0.popitem()[1]
                        elif 1 not in visited :
                            c = half1.popitem()[1]
                        else :
                            c = half2.popitem()[1]
                            
                        # In this case we return out of order
                        # if a.index > b.index :
                        #     a,b = b,a
                        # if b.index > c.index :
                        #     b,c = c,b
                        # if a.index > b.index :
                        #     a,b = b,a                        
                        
                        return a, b, c
                            
        ## Let us try shattered. There is no balanced here.
        for key in list(half0.keys()) :
            if (key != v_i.cycle) :
                a,b,c = None, None, None
                if key in half1 :
                    a,c = half0[key], half1[key]
                    b   = half2.popitem()[1] ## Primeiro node do dicionario
                if key in half2 :
                    a,b = half0[key], half2[key]
                    c   = half1.popitem()[1] ## Primeiro node do dicionario
                if ( a and b and c ) :
                    if a.index > c.index :
                        return b, c, a
                    else :
                        return a, b, c
        print("""ERROR: this line should never be reached, are you sure you removed the oriented cycles? """)

    ## Here we have a transposition where a and b are in the same
    ## cycle and need to get rid of weight to send to c. We need to
    ## guaratee that the cycle that will be generated by C=(...a...b)
    ## and will not contain c is balanced.
    def __compute_weight_to_send_to_other_cycle(self, a, b, c) :
        if a.index > b.index :
            a,b = b,a
            
        ## when c is between a and b, the inner
        ## edge of the blackmost cycle will be
        ## alone in a cycle. So, I will replace a
        ## and b again.
        if a.index < c.index < b.index :
            blacks, grays = self.__sum_weight_in_segment(b, a)            
            blacks = blacks - b.wp[0]
            balance = grays - blacks
            if 0 <= balance <= b.wp[0] + a.wp[0] :                            
                wa = min(balance, a.wp[0])
                wb = balance - wa
                wa = a.wp[0] - wa
                #return a, c, b, wa, c.wp[0], wb
                return (3, a, c, b, [[wa], [a.wp[0] - wa + wb], [c.wp[0] + b.wp[0]-wb]])
            else :
                return None
        else :
            blacks, grays = self.__sum_weight_in_segment(a, b)
            blacks = blacks - a.wp[0]
            balance = grays - blacks
            if 0 <= balance <= a.wp[0] + b.wp[0] :                            
                wa = min(balance, a.wp[0])
                wb = b.wp[0] - (balance - wa)
                if c.index < a.index :
                    #return (c, a, b, c.wp[0], wa, wb)
                    return (3, c, a, b, [[c.wp[0] + a.wp[0]-wa], [wb], [b.wp[0]-wb + wa]])
                else :
                    #return (a, b, c, wa, wb, c.wp[0])
                    return (3, a, b, c, [[wa + b.wp[0] - wb], [a.wp[0]-wa + c.wp[0]], [wb]])
            else :
                return None


    ## Here we have a transposition where a and b are in the same
    ## cycle and need to get rid of weight to send to c. We need to
    ## guaratee that the cycle that will be generated by C=(...a...b)
    ## and will not contain c is balanced.
    def __compute_weight_to_send_to_other_cycle_two_short(self, a, b, c) :
        if a.index > b.index :
            a,b = b,a

        ## when c is between a and b, the inner
        ## edge of the blackmost cycle will be
        ## alone in a cycle. So, I will replace a
        ## and b again.
        if a.index < c.index < b.index :
            c = c.ap.ac
        #     blacks, grays = self.__sum_weight_in_segment(b, a)
        #     blacks = blacks - b.wp[0]
        #     balance = grays - blacks
        #     if 0 <= balance <= b.wp[0] + a.wp[0] :
        #         wa = min(balance, a.wp[0])
        #         wb = balance - wa
        #         wa = a.wp[0] - wa
        #         #return a, c, b, wa, c.wp[0], wb
        #         #print("cw1")
        #         return (3, a, c, b, [[wa], [a.wp[0] - wa + wb], [c.wp[0] + b.wp[0]-wb]])
        #     else :
        #         return None
        # else :
        if c.index < a.index :
            d = c.ap.ac
            wb = b.wp[0] - max(0,b.wc[0] - a.wp[0])
            wa = b.wc[0] - (b.wp[0] - wb)
            wc = max(0,min(c.wp[0], d.wc[0] - d.wp[0]))
            return (3, c, a, b, [[wc + a.wp[0]-wa], [wb+c.wp[0]-wc], [b.wp[0]-wb + wa]])
        if c.index > b.index :
            d = c.ap.ac
            wa = min(b.wc[0], a.wp[0])
            wb = b.wp[0] - (b.wc[0] - wa)
            wc = max(0,min(c.wp[0], c.wc[0] - d.wp[0]))
            return (3, a, b, c, [[wa + b.wp[0] - wb], [a.wp[0]-wa + wc], [c.wp[0] - wc + wb]])
        else :
            print("I had a problem when finding the short crossing cycle...")
            sys.exit(0)


    ## At this point, we know that no oriented balanced cycle exists.
    def lemma_4_transp(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].direction == 1 and ## Check if it is convergent
                cycle[0].size      >=  3 and ## Check if it is long
                cycle[0].blacks    == cycle[0].grays and # Check if it is balanced
                cycle[0].gray_labeled == False and                 # not gray labeled, and
                cycle[0].black_labeled == False                     # not black labeled
            ) :
                ## The following link works because no oriented
                ## balanced exists.
                transp = self.__search_interleaving_edges(
                    graph,
                    cycle[4],
                    cycle[2],
                    cycle[0])

                ## If it is a shuffling transposition, we can do it.
                if transp[0].cycle == transp[1].cycle == transp[2].cycle :
                    return (3, transp[0], transp[1], transp[2],
                            [[transp[0].wp[0]],
                            [transp[2].wp[0]],
                            [transp[1].wp[0]]])
                ## If the cycles are unbalanced, we can do it.
                if ( (transp[0].blacks != transp[0].grays) and
                     (transp[1].blacks != transp[1].grays) and
                     (transp[2].blacks != transp[2].grays) ) :
                    return (3, transp[0], transp[1], transp[2],
                            [[transp[0].wp[0]],
                            [transp[2].wp[0]],
                            [transp[1].wp[0]]])
                
                ## At least one of them is balanced. So we need to be
                ## careful at this point. We need to move a balanced
                ## amount of weight.  We know that
                ## self.__search_interleaving_edges places the
                ## balanced cycle first, which is great. Also, the
                ## returned edges are already the ones we can break,
                ## we just need to compute weights.
                return self.__compute_weight_to_send_to_other_cycle(transp[0], transp[1], transp[2])

    
            
    ## At this point, we know that no oriented balanced cycle exists.
    def search_nontrivial_unbalanced_transposition(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].direction == 1 and ## Check if it is convergent
                cycle[0].size      >= 2 and ## Check if it is nontrivial
                cycle[0].blacks    > cycle[0].grays 
            ) :
                ## Let us first find another cycle where we will put
                ## the extra weight.
                c = None
                for cycle1 in vertices :
                    if (cycle1[0].blacks  < cycle1[0].grays) :
                        c = cycle1[0]
                        break
                    
                ## Let us find a long cycle
                init = cycle[0]
                end  = init.ap.ac
                while True : ## I will be locked in this infinity loop
                             ## to depure if something fails
                    while end != init :
                        op = self.__compute_weight_to_send_to_other_cycle(init, end, c) 
                        if op :
                            return op
                        end = end.ap.ac
                    init = init.ap.ac
                    end  = init.ap.ac
                    if init == cycle[0] :
                        break

    def __make_sure_the_three_cycles_are_balanced(self, graph, node0, node1, node2) :
        ops = []
        if node0.grays == node0.blacks :
            triv_bal, a, b = node0, node1, node2
        elif node1.grays == node1.blacks :
            triv_bal, a, b = node1, node0, node2
        elif node2.grays == node2.blacks :
            triv_bal, a, b = node2, node0, node1
        else :
            print("Error after applying lemma 3, no balanced cycles were generated...")
            sys.exit(0)

        if (a.grays != a.blacks) and (b.grays != b.blacks) :
            if (a.blacks > a.grays) :
                if a.size == 1 :
                    diference = int(a.blacks-a.grays)
                    ops.append((0, a.ap, 0, [[], [diference,]]))
                    ops.append((1, b.ap, 0, [[], [diference,]]))
                else :
                    _, vertices = graph.get_cycles(want_vertices = True)
                    for cycle in vertices :
                        if (cycle[0].cycle == a.cycle) :
                            c = None
                            for cycle1 in vertices :
                                if (cycle1[0].cycle == b.cycle) :
                                    c = cycle1[0]
                                    break

                            ## Let us find a long cycle
                            init = cycle[0]
                            end  = init.ap.ac
                            while True : ## I will be locked in this infinity loop
                                         ## to depure if something fails
                                while end != init :
                                    op = self.__compute_weight_to_send_to_other_cycle(init, end, c)
                                    if op :
                                        return [op]
                                    end = end.ap.ac
                                init = init.ap.ac
                                end  = init.ap.ac
                                if init == cycle[0] :
                                    break
            else :
                if b.size == 1 :
                    diference = int(b.blacks-b.grays)
                    ops.append((0, b, 0, [[], [diference,]]))
                    ops.append((1, a, 0, [[], [diference,]]))
                else :
                    _, vertices = graph.get_cycles(want_vertices = True)
                    for cycle in vertices :
                        if (cycle[0].cycle == b.cycle) :
                            c = None
                            for cycle1 in vertices :
                                if (cycle1[0].cycle == a.cycle) :
                                    c = cycle1[0]
                                    break

                            ## Let us find a long cycle
                            init = cycle[0]
                            end  = init.ap.ac
                            while True : ## I will be locked in this infinity loop
                                         ## to depure if something fails
                                while end != init :
                                    op = self.__compute_weight_to_send_to_other_cycle(init, end, c)
                                    if op :
                                        return [op]
                                    end = end.ap.ac
                                init = init.ap.ac
                                end  = init.ap.ac
                                if init == cycle[0] :
                                    break
        return ops


    def __search_trivial_unbalanced_transposition(self, node0, node1, node2) :
        a,b,c = node0, node1, node2
        
        #ANDRE changed the following two lines
        wa, wb, wc = 0, 0, c.wp[0]
        #wa, wb, wc = a.wc[0], b.wp[0], c.wp[0]

        if a.index > b.index :
            a,b = b,a
            wa, wb = wb, wa
        if b.index > c.index :
            b,c = c,b
            wb, wc = wc, wb
        if a.index > b.index :
            a,b = b,a
            wa, wb = wb, wa

        #BEGIN ANDRE ADDED THIS HELPS TO GET BETTER RESULTS BUT IT IS NOT IN THE PROOF
        ## If there are three cycles such that the sum of grays and blacks are equal,
        ## we are going to change A, B and C to balance the three with 2 operations
        if (a.wp[0] + b.wp[0] + c.wp[0]) == (a.wc[0] + b.wc[0] + c.wc[0]) and a.blacks == a.wp[0] and b.blacks == b.wp[0] and c.blacks == c.wp[0]:
            if node0 == a:
                wa, wb, wc = min(a.wp[0],max(a.wc[0],a.wc[0]+b.wc[0]-b.wp[0])), b.wp[0], 0
                awpnew = wa      + 0
                bwpnew = a.wp[0]-wa + 0
                cwpnew = b.wp[0]    + c.wp[0]
                wa2, wb2, wc2 = a.wc[0], bwpnew, cwpnew+bwpnew-c.wc[0]
            elif node0 == b:
                wa, wb, wc = min(a.wp[0],a.wc[0]), b.wp[0]-min(b.wp[0],max(0,a.wc[0]-a.wp[0])), c.wp[0]-min(c.wp[0],c.wc[0])
                awpnew = wa      + b.wp[0]-wb
                cwpnew = c.wp[0]-wc + wb
                bwpnew = a.wp[0]-wa + wc
                wa2, wb2, wc2 = min(a.wc[0],awpnew), bwpnew-(a.wc[0]-awpnew), b.wc[0]-(awpnew-min(a.wc[0],awpnew))
            else:
                wa, wb, wc = a.wp[0], 0, c.wp[0]-min(c.wp[0],c.wc[0]+b.wc[0])
                awpnew = a.wp[0]    + b.wp[0]
                cwpnew = c.wp[0]-wc  + 0
                bwpnew = wc + 0
                wa2, wb2, wc2 = min(awpnew,a.wc[0]), 0, cwpnew-c.wc[0]
        ## Otherwise, just move positive balance from cycle0 (a)
        ## to node1 (b) and leave node2 (c) unchanged
        else:
        #if True:
            if node2 == a:
                #2022#wa, wb, wc = a.wp[0], b.wp[0], 0 
                wa, wb, wc = [a.wp[0]], [0], [b.wp[0] + c.wp[0]]
                if node0 == b:
                    #2022#wa2, wb2, wc2 = a.wp[0], 0, b.wc[0]
                    wa2, wb2, wc2 = [a.wp[0]], [b.wc[0]], [c.wp[0] + b.wp[0]-b.wc[0]]
                else:
                    #2022#wa2, wb2, wc2 = a.wp[0], 0, b.wp[0]+c.wp[0]-c.wc[0]
                    wa2, wb2, wc2 = [a.wp[0]], [b.wp[0]+c.wp[0]-c.wc[0]], [c.wc[0]]
            elif node2 == b:
                #2022#wa, wb, wc = 0, b.wp[0], c.wp[0]
                wa, wb, wc = [0], [a.wp[0] + c.wp[0]], [b.wp[0]]
                if node0 == a:
                    #2022#wa2, wb2, wc2 = 0, a.wp[0]+c.wp[0]-a.wc[0], b.wp[0]
                    wa2, wb2, wc2 = [a.wc[0]], [b.wp[0]], [a.wp[0]+c.wp[0]-a.wc[0]]
                else:
                    #2022#wa2, wb2, wc2 = 0, c.wc[0], b.wp[0]
                    wa2, wb2, wc2 = [a.wp[0]+c.wp[0]-c.wc[0]], [b.wp[0]], [c.wc[0]]
            else: # node2 == c
                #2022#wa, wb, wc = a.wp[0], 0, 0
                wa, wb, wc = [a.wp[0] + b.wp[0]], [0], [c.wp[0]]
                if node0 == a:
                    #2022#wa2, wb2, wc2 = a.wc[0], 0, 0 #fix
                    wa2, wb2, wc2 = [a.wc[0]], [a.wp[0]+b.wp[0]-a.wc[0]], [c.wp[0]] #fix
                else:
                    #2022#wa2, wb2, wc2 = a.wp[0]+b.wp[0]-b.wc[0], 0, 0 #fix
                    wa2, wb2, wc2 = [a.wp[0]+b.wp[0]-b.wc[0]], [b.wc[0]], [c.wp[0]] #fix
        #END ANDRE ADDED THIS

        return [(3, a, b, c, [wa, wb, wc]),(3, b, a, c, [wa2, wb2, wc2])]

        

    ## At this point, we know that no blackheaviest cycle is bigger
    ## than 1. Therefore we have little ammunition, our last resource
    ## is to send the extra weight somewhere.
    def search_trivial_unbalanced_transposition(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].blacks    > cycle[0].grays) :

                ## Search for other gray edges where we will send the
                ## extra weight.
                node1, node2 = None, None
                node = graph.end_node                
                while node :
                    #####ANDRE changed != to <
                    if (node.blacks < node.grays and
                        node.cycle  != cycle[0].cycle) :
                        if   not node1 :
                            node1 = node
                        else :
                            node2 = node
                            break
                    node = node.ap.ab

                ## There is only two unbalanced cycles and they are
                ## trivial, so I pick any cycle as node2.
                node = graph.end_node
                while not node2 :
                    if (node.index != node1.index and
                        node.index != cycle[0].index) :
                        node2 = node
                    node = node.ap.ab

                return self.__search_trivial_unbalanced_transposition(cycle[0], node1, node2)



    def __search_two_trivial_unbalanced_transposition(self, node0, node1, node2) :  
        a,b,c = node0, node1, node2

        #ANDRE changed the following two lines
        wa, wb, wc = 0, 0, c.wp
        #wa, wb, wc = a.wc, b.wp, c.wp

        if a.index > b.index :
            a,b = b,a
            wa, wb = wb, wa
        if b.index > c.index :
            b,c = c,b
            wb, wc = wc, wb
        if a.index > b.index :
            a,b = b,a
            wa, wb = wb, wa

        ### Verifica se node1 tambem eh negativo, se sim apenas node2 eh positivo
        ### e manda todo o excesso pra ele
        if node1.blacks > node1.grays:
            if node2 == a:
                wa = a.wp
                wb = b.wc
                wc = c.wp - c.wc
                wa2 = a.wp + (b.wp-b.wc) 
                wb2 = 0
                wc2 = b.wc
                return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

            elif node2 == b:
                wa = a.wp
                wb = b.wp
                wc = 0
                wa2 = a.wc
                wb2 = 0
                wc2 = b.wp+c.wp-c.wc
                return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

            else:
                wa = a.wc
                wb = b.wp-b.wc
                wc = 0
                wa2 = a.wc
                wb2 = a.wp-a.wc
                wc2 = 0
                return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]


        elif (node2.cycle == node1.cycle) or (node2.grays == node2.blacks):
            if node2 == a:
                if node0 == b: #node1 == c
                    wa = a.wp
                    wb = b.wp
                    wc = 0
                    wa2 = a.wp
                    wb2 = 0
                    wc2 = b.wc
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

                else: #node0 == c node1 == b
                    wa = a.wp
                    wb = b.wp
                    wc = 0
                    wa2 = a.wp
                    wb2 = 0
                    wc2 = wb+b.grays-b.blacks
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

            elif node2 == b:
                if node0 == a: #node1 == c
                    wa = a.wc
                    wb = b.wp
                    wc = 0
                    wa2 = a.wc
                    wb2 = a.wp-wa
                    wc2 = b.wp
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

                else: #node0 == c node1 == a
                    wa = a.wp
                    wb = 0
                    wc = c.wp - c.wc
                    wa2 = a.wp
                    wb2 = 0
                    wc2 = 0
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

            else: #node2 == c
                if node0 == a: #node1 == b
                    wa = a.wp
                    wb = 0
                    wc = 0
                    wa2 = a.wc
                    wb2 = 0
                    wc2 = 0
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

                else: #node0 == b node1 == a
                    wa = a.wp
                    wb = 0
                    wc = 0
                    wa2 = a.wp+b.wp-b.wc
                    wb2 = 0
                    wc2 = 0
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

        else:
            if node2.cycle != node1.cycle:
                if node0 == a:
                    wa = a.wc + (b.grays - b.blacks)
                    wb = 0
                    wc = 0
                    wa2 = a.wc
                    wb2 = a.wp - wa
                    wc2 = 0
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

                elif node0 == b:
                    wa = a.wp
                    wb = b.grays + c.grays-c.blacks ##c.grays-c.blacks
                    wc = 0
                    wa2 = wa + b.wp - wb ##b.wc
                    wb2 = 0
                    wc2 = b.grays ##0
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

                else: #node0 == c
                    need_a = a.grays-a.blacks
                    need_b = b.grays-b.blacks
                    wa = a.wp
                    wb = b.wp
                    wc = c.wp - c.wc - need_b
                    wa2 = a.wp
                    wb2 = 0
                    wc2 = need_b + wb #b.grays #b.grays-b.blacks
                    return [[a, b, c, wa, wb, wc],[b, a, c, wa2, wb2, wc2]]

        print("ERRO Ops, nenhuma operacao encontrada...")
        sys.exit()


    ## At this point, we know that no blackheaviest cycle is bigger
    ## than 1. Therefore we have little ammunition, our last resource
    ## is to send the extra weight somewhere. The trick here is that
    ## we can find either two negative, or two positives or one of each
    ## and create two new balanced cycles
    def search_two_trivial_unbalanced_transposition(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].blacks    > cycle[0].grays) :

                ## Search another cycle that is also negative to be node1
                node1, node2 = None, None
                node = graph.end_node                
                while node :
                    if (node.blacks > node.grays and node.cycle != cycle[0].cycle) :
                        if   not node1 :
                            node1 = node
                    node = node.ap.ab

                ## If node1 is None, then let us choose a positive cycle to be node1
                if not node1:
                    node = graph.end_node                
                    while node :
                        if (node.blacks < node.grays and node.cycle != cycle[0].cycle) :
                            if not node1 :
                                node1 = node
                        node = node.ap.ab
                
                ## Let us find now a positive cycle (that is different from node1) to be node2
                node = graph.end_node                
                while node :
                    if (node.blacks < node.grays and node.cycle != node1.cycle) :
                        if   not node2 :
                            node2 = node
                    node = node.ap.ab

                ## There is only two unbalanced cycles, so I pick any balanced cycle as node2.
                node = graph.end_node
                while not node2 :
                    if (node.index != node1.index and
                        node.index != cycle[0].index) :
                        node2 = node
                    node = node.ap.ab

                return self.__search_two_trivial_unbalanced_transposition(cycle[0], node1, node2)


    ## Search crossing edges. The point of this method is to find a
    ## reversal that transforms two black edges that are convergent
    ## into two black edges that are divergent. I will usually put
    ## these two black edges as parameters.
    def __search_crossing_edges_for_transposition(self, graph, v_i, v_j) :
        ## b is the rightmost and in the right side of the black edge
        a,b = v_i, v_j
        if a.index > b.index :
            a,b = b,a
        if a.index % 2 == 0 :
            a = a.ap
        if b.index % 2 == 0 :
            b = b.ap

        half1 = {}
        half2 = {}
        
        ## starting the search
        node = graph.end_node
        while node != b :
            half1[node.cycle] = node
            node = node.ap.ab
                    
        node = b.ap.ab
        while node != a :
            half2[node.cycle] = node
            node = node.ap.ab        
        node = a.ap.ab
        while node :
            half1[node.cycle] = node
            node = node.ap.ab

        for key in list(half1.keys()) :
            if key in half2 :
                a,b = half1[key], half2[key]
                if ( key != v_i.cycle  ) :
                    if a.index > b.index :
                        a,b = b,a
                    return a,b

            
    def lemma_5_transp(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (
                cycle[0].size          ==  2    and                 # non-trivial
                cycle[0].gray_labeled  == False and                 # not gray labeled, and
                cycle[0].black_labeled == False                     # not black labeled
               ) :
                a,b = cycle[0].ap.ac, cycle[0]
                c,d = self.__search_crossing_edges_for_transposition(graph, a, b)
                op = self.__compute_weight_to_send_to_other_cycle_two_short(a, b, c)
                if op :
                    return op

    def lemma_6_transp(self, graph) :
        return self.lemma_5(graph)


    def lemma_7_transp(self, graph) :
        return self.lemma_6(graph)

    def lemma_8_transp(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (
                  cycle[0].size > 1 and                # non-trivial,
                  cycle[0].blacks < cycle[0].grays and # positive,
                  cycle[0].gray_labeled  == False and                 # not gray labeled, and
                  cycle[0].black_labeled == False                     # not black labeled
            ) : ## we just increase the weight of the black edge
                indel_position = 0
                indel_sequence = [int(cycle[0].grays - cycle[0].blacks),]
                pi_inserted = []
                return (1, cycle[0], indel_position, [pi_inserted, indel_sequence])
        return None


    def lemma_9_transp(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].direction == 1 and ## Check if it is convergent
                cycle[0].size      >= 3 and ## Check if it is long
                not (cycle[0].gray_labeled == False and cycle[0].black_labeled == False and cycle[0].blacks == cycle[0].grays) ## Check if it is a bad cycle
            ) :
                triples = self.find_all_triples_two_adj(cycle)
                
                if not triples :
                    return None
              
                # first let us try to create a balanced good cycle if possible
                for transp in triples :
                    #trivial in the left
                    if transp[0].ap.ac == transp[1] and len(transp[1].wc) == 1 :
                        if transp[0].wp[0] + transp[1].wp[-1] >= transp[1].wc[0] :
                            from_left = min(transp[0].wp[0],transp[1].wc[0])
                            from_middle = transp[1].wc[0] - from_left
                            left_w = [] + transp[1].wc
                            middle_w = [transp[0].wp[0]-from_left] + transp[0].wp[1:]
                            right_w = transp[1].wp[:-1] + [transp[1].wp[-1]-from_middle + transp[2].wp[0]] + transp[2].wp[1:]
                            return (3, transp[0], transp[1], transp[2], [left_w, middle_w, right_w])
                    
                    if transp[1].ap.ac == transp[2] and len(transp[2].wc) == 1 :
                        #trivial formado na direita
                        if transp[1].wp[0] + transp[2].wp[-1] >= transp[2].wc[0] :
                            from_middle = min(transp[1].wp[0],transp[2].wc[0])
                            from_right = transp[2].wc[0] - from_middle
                            left_w = transp[0].wp[:-1] + [transp[0].wp[-1] + transp[1].wp[0]-from_middle] + transp[1].wp[1:]
                            middle_w = transp[2].wp[:-1] + [transp[2].wp[-1]-from_right]
                            right_w = [] + transp[2].wc
                            return (3, transp[0], transp[1], transp[2], [left_w, middle_w, right_w])
                    
                    if transp[2].ap.ac == transp[0] and len(transp[0].wc) == 1 :
                        #trivial formado no meio
                        if transp[2].wp[0] + transp[0].wp[-1] >= transp[0].wc[0] :
                            from_left = min(transp[0].wp[-1],transp[0].wc[0])
                            from_right = transp[0].wc[0] - from_left
                            left_w = transp[0].wp[:-1] + [transp[0].wp[-1]-from_left]
                            middle_w = [] + transp[0].wc
                            right_w = transp[1].wp[:-1] + [ transp[1].wp[-1] + transp[2].wp[0] - from_right ] + transp[2].wp[1:]
                            return (3, transp[0], transp[1], transp[2], [left_w, middle_w, right_w])

                # it is not possible, so let us just create a trivial cycle and set 0 to its black edge weight
                transp = triples[0]
                if transp[0].ap.ac == transp[1] :
                    #trivial formado na esquerda
                    left_w   = [0]
                    middle_w = [] + transp[0].wp
                    right_w  = transp[1].wp[:-1] + [transp[1].wp[-1] + transp[2].wp[0]] + transp[2].wp[1:]
                    return (3, transp[0], transp[1], transp[2], [left_w, middle_w, right_w])
                
                if transp[1].ap.ac == transp[2] :
                    #trivial formado na direita
                    left_w   = transp[0].wp[:-1] + [transp[0].wp[-1] + transp[1].wp[0] ] + transp[1].wp[1:]
                    middle_w = [] + transp[2].wp
                    right_w  = [0]
                    return (3, transp[0], transp[1], transp[2], [left_w, middle_w, right_w])
                
                else :# if transp[2].ap.ac == transp[0] :
                    #trivial formado no meio
                    left_w   = [] + transp[0].wp
                    middle_w = [0]
                    right_w  = transp[1].wp[:-1] + [ transp[1].wp[-1] + transp[2].wp[0] ] + transp[2].wp[1:]
                    return (3, transp[0], transp[1], transp[2], [left_w, middle_w, right_w])



    def lemma_10_transp(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        bad_ones = []
        for cycle in vertices :
            if (cycle[0].direction == 1 and ## Check if it is convergent
                cycle[0].size      > 1 and ## Check if it is non trivial
                not (cycle[0].gray_labeled == False and cycle[0].black_labeled == False and cycle[0].blacks == cycle[0].grays) ## Check if it is a bad cycle
            ) :
                bad_ones.append(cycle[0])

        if len(bad_ones) > 1 :
            first_cycle = bad_ones[0]
            second_cycle = bad_ones[1]

            if second_cycle.index > first_cycle.index :
                transp = [first_cycle.ac.ap, first_cycle, second_cycle]
            else :
                transp = [second_cycle.ac.ap, second_cycle, first_cycle]

            # if it is possible to create a good trivial cycle, why not?
            if len(transp[1].wc) == 1 and transp[0].wp[0] + transp[1].wp[-1] >= transp[1].wc[0] :
                from_left = min(transp[0].wp[0],transp[1].wc[0])
                from_middle = transp[1].wc[0] - from_left
                left_w = [] + transp[1].wc
                middle_w = [transp[0].wp[0]-from_left] + transp[0].wp[1:]
                right_w = transp[1].wp[:-1] + [transp[1].wp[-1]-from_middle + transp[2].wp[0]] + transp[2].wp[1:]
                return (3, transp[0], transp[1], transp[2], [left_w, middle_w, right_w])
            # otherwise we create a trivial cycle and set [0] to its black edge
            else :
                left_w   = [0]
                middle_w = [] + transp[0].wp
                right_w  = transp[1].wp[:-1] + [transp[1].wp[-1] + transp[2].wp[0]] + transp[2].wp[1:]
                return (3, transp[0], transp[1], transp[2], [left_w, middle_w, right_w])

        return None


    def lemma_11_transp(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        bad_ones = []
        for cycle in vertices :
            if (cycle[0].direction == 1 and ## Check if it is convergent
                cycle[0].size       > 1 and ## Check if it is non trivial
                not (cycle[0].gray_labeled == False and cycle[0].black_labeled == False and cycle[0].blacks == cycle[0].grays) ## Check if it is a bad cycle
            ) :
                bad_ones.append(cycle)
        if len(bad_ones) == 1 :
            cycle = bad_ones[0]
            if cycle[0].size > 2 :
                return None
            if cycle[0].gray_labeled == False :
                if cycle[0].black_labeled == False :
                    # no labels at all! just apply an indel adding or removing intergenic regions
                    ops = []
                    indel_position = 0
                    operation = 0
                    pi_inserted = []
                    if cycle[0].grays > cycle[0].blacks :
                        operation = 1
                        indel_sequence = [int(cycle[0].grays - cycle[0].blacks)]
                        ops.append((operation, cycle[2], indel_position, [pi_inserted, indel_sequence]))
                    else :
                        to_remove = int(cycle[0].blacks - cycle[0].grays)
                        if cycle[0].wp[0] >= to_remove:
                            indel_sequence = [to_remove,]
                            ops.append((operation, cycle[0], indel_position, [pi_inserted, indel_sequence]))
                        elif  cycle[2].wp[0] >= to_remove:
                            indel_sequence = [to_remove,]
                            ops.append((operation, cycle[2], indel_position, [pi_inserted, indel_sequence]))
                        else :
                            indel_sequence0 = [cycle[0].wp[0]]
                            indel_sequence2 = [int(to_remove-cycle[0].wp[0])]
                            ops.append((operation, cycle[0], indel_position, [pi_inserted, indel_sequence0]))
                            ops.append((operation, cycle[2], indel_position, [pi_inserted, indel_sequence2]))
                    return ops
                else :
                    ops, is_bal = [], cycle[0].grays == cycle[0].blacks
                    if cycle[0].grays > cycle[0].blacks :
                        ops.append((1, cycle[2], 0, [[], [int(cycle[0].grays - cycle[0].blacks),]]))
                        is_bal = True
                    to_remove = 0 if is_bal else cycle[0].blacks - cycle[0].grays
                    if len(cycle[0].wp) > 1 :
                        indel_position_0 = cycle[0].wp[0] - to_remove if cycle[0].wp[0] >= to_remove else 0
                        if to_remove :
                            to_remove -= (cycle[0].wp[0] - indel_position_0)
                        indel_sequence_0 = [cycle[0].wp[0] - indel_position_0] + cycle[0].wp[1:-1] + [to_remove if to_remove < cycle[0].wp[-1] else cycle[0].wp[-1] ]
                        if to_remove :
                            to_remove -= indel_sequence_0[-1]
                        ops.append((0, cycle[0], indel_position_0, [[0 for _ in range(0,cycle[0].lp)], indel_sequence_0]))
                    if len(cycle[2].wp) > 1 :
                        indel_position_1 = cycle[2].wp[0] - to_remove if cycle[2].wp[0] >= to_remove else 0
                        if to_remove :
                            to_remove -= (cycle[2].wp[0] - indel_position_1)
                        indel_sequence_1 = [cycle[2].wp[0] - indel_position_1] + cycle[2].wp[1:-1] + [to_remove if to_remove < cycle[2].wp[-1] else cycle[2].wp[-1] ]
                        if to_remove :
                            to_remove -= indel_sequence_1[-1]
                        ops.append((0, cycle[2], indel_position_1, [[0 for _ in range(0,cycle[0].lp)], indel_sequence_1]))

                    if to_remove != 0 and len(cycle[0].wp) == 1 and cycle[0].wp[0] >= to_remove :
                        ops.append((0, cycle[0], 0, [[], [to_remove,]]))
                        to_remove = 0
                    if to_remove != 0 and len(cycle[2].wp) == 1 and cycle[2].wp[0] >= to_remove :
                        ops.append((0, cycle[2], 0, [[], [to_remove,]]))
                        to_remove = 0

                    # at this point if to_remove is not 0 then we have a serious problem...
                    if to_remove != 0 :
                        print("Error in Lemma 11... the indels kept the cycle unbalanced")
                        sys.exit(0)
                    return ops
            else : #we also have gray labeled edges...
                # at this time I will apply only an insertion. in the next
                # iteration the above if will clean the black edges using no
                # more than two operations, since this insertion below
                # guarantees that the cycle will be non-positive
                pi_inserted = [cycle[0].lc_iota, cycle[2].lc_iota]
                if not pi_inserted[0] or not pi_inserted[1] :
                    to_add = max(0, cycle[0].wc[-1] + cycle[2].wc[0] - cycle[0].wps - cycle[2].wps)
                else :
                    to_add = max(0, cycle[0].wc[-1] + cycle[2].wc[0] - cycle[0].wps)
                #######################################################
                if pi_inserted[0] :
                    if ((cycle[0].index > cycle[0].ap.index and cycle[0].value > 0) or
                       (cycle[0].index < cycle[0].ap.index and cycle[0].value < 0)) :
                        pi_inserted[0] = [-i for i in pi_inserted[0][::-1]]
                        cycle[0].wc = cycle[0].ap.wc = cycle[0].wc[::-1]
                if pi_inserted[1] :
                    if ((cycle[2].index > cycle[2].ap.index and cycle[2].value > 0) or
                       (cycle[2].index < cycle[2].ap.index and cycle[2].value < 0)) :
                        pi_inserted[1] = [-i for i in pi_inserted[1][::-1]]
                        cycle[2].wc = cycle[2].ap.wc = cycle[2].wc[::-1]
                #######################################################
                if len(cycle[0].wc) > 1 and len(cycle[2].wc) > 1 :
                    indel_position = 0
                    indel_sequence = cycle[0].wc[:-1] + [int(to_add)] + cycle[2].wc[:-2] + [ [cycle[2].wc[-1] + cycle[0].wp[0]] + cycle[0].wp[1:] ]
                elif len(cycle[0].wc) > 1 :
                    indel_position = 0
                    indel_sequence = cycle[0].wc[:-1] + [[int(to_add + cycle[2].wp[0])] + cycle[2].wp[1:]]
                else :
                    indel_position = sum(cycle[0].wp)
                    indel_sequence = [cycle[2].wp[:-1] + [int(to_add + cycle[2].wp[-1])]] + cycle[2].wc[1:]
                return [(1, cycle[0], indel_position, [pi_inserted, indel_sequence])]



    def lemma_12_transp(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        bad_ones = []
        for cycle in vertices :
            if (cycle[0].direction == 1 and ## Check if it is convergent
                cycle[0].size      > 1 and ## Check if it is non trivial
                not (cycle[0].gray_labeled == False and cycle[0].black_labeled == False and cycle[0].blacks == cycle[0].grays) ## Check if it is a bad cycle
            ) :
                bad_ones.append(cycle)

        if len(bad_ones) == 1 :
            cycle = bad_ones[0]
            if cycle[0].size == 2 :
                return None
            transp = self.__search_interleaving_edges(
                graph,
                cycle[4],
                cycle[2],
                cycle[0])

            ## just one cycle
            if transp[0].cycle == transp[1].cycle == transp[2].cycle :
                return (3, transp[0], transp[1], transp[2],
                        [[transp[0].wp[0]],
                        [transp[2].wp[0]],
                        [transp[1].wp[0]]])
            ## there are two cycles
            else :
                return self.__compute_weight_to_send_to_other_cycle(transp[0], transp[1], transp[2])




########################################################################## 
## Auxiliary functions to transform the input into the instance we want
##########################################################################       

def get_position(permutation) :
    n = len(permutation)-2
    position    = [-1 for i in range(0, n+2)]
    for i in range(0, n+2) :
        position[abs(permutation[i])] = i
    return position

def get_rightmost_element(cycle, position) :
    max_position = 0
    for i in range(len(cycle)) :
        if position[cycle[i]] > position[cycle[max_position]] :
            max_position = i
    return max_position

## The unordered cycle starts with a gray edge, we order them by
## making it start with the rightmost black edge.
def order_cycle(cycle, position) :
    index = get_rightmost_element(cycle, position)
    new   = []
    new.append(cycle[index])

    if index % 2 == 0 :
        iter_el  = (index-1) % len(cycle)
        while iter_el != index :
            new.append(cycle[iter_el])
            iter_el = (iter_el-1) % len(cycle)
    else :
        iter_el  = (index+1) % len(cycle)
        while iter_el != index :
            new.append(cycle[iter_el])
            iter_el = (iter_el+1) % len(cycle)
    return new

def canonical_representation(cycle, position) :
    cycle     = order_cycle(cycle, position)
    canonical = []

    for i in range(0,len(cycle),2) :
        if position[cycle[i]] < position[cycle[i+1]] :
            black = -position[cycle[i+1]]
            canonical.append(black )
        else :
            black = position[cycle[i]]
            canonical.append(black)
    return canonical

def construct_black_edges(input_string, input_black) :
    wblack = []
    input_string_numbers = []
    interblack = []
    for i in range(0,len(input_string)) :
        num = input_string[i]
        interblack.append(input_black[i])
        if num != 0 :
            input_string_numbers.append(num)
            wblack.append(interblack)
            interblack = []

    i = len(input_string)
    while i < len(input_black) :
        interblack.append(input_black[i])
        i += 1
    if len(interblack) > 0 :
        wblack.append(interblack)
    return(wblack, input_string_numbers)

def construct_str_cycle(input_string, input_gray, input_black) :

    # Given the input_black weights, let us group them according
    # to the edges in the cycle graph (i.e., we just group the
    # values on positions where input_string is 0)
    wblack, input_string_numbers = construct_black_edges(input_string, input_black)

    # Get the maximum number in input_string and add the paddings (i.e., 0 and n+1)
    max_input_string_numbers = max(max(input_string_numbers),-1*min(input_string_numbers))
    input_string_numbers = [0] + input_string_numbers + [max_input_string_numbers+1]

    # This is a vector that says if an element is present or not in the input_string
    element_exists = [-1 for i in range(0,max_input_string_numbers+2)]
    for element in input_string_numbers :
        element_exists[abs(element)] = 0

    # Sort the elements in the input_string to help with the gray edges generation
    sorted_input_string = [abs(el) for el in input_string_numbers]
    sorted_input_string.sort()

    # Here we genarate the gray edges weights using the input_gray
    wgray = []
    for i in range(1,len(sorted_input_string)-1) :
        intergray = input_gray[sorted_input_string[i-1]:sorted_input_string[i]]
        wgray.append(intergray)
    intergray = input_gray[sorted_input_string[i]:]
    wgray.append(intergray)

    # Now we generate a corresponding permutation using the input_string
    acc = 0
    for i in range(0,len(element_exists)) :
        acc += element_exists[i]
        element_exists[i] = acc
    permutation = []
    for i in range(0,len(input_string_numbers)) :
        curr = abs(input_string_numbers[i])
        curr += element_exists[curr]

        if input_string_numbers[i] < 0 :
            permutation.append(-curr)
        else :
            permutation.append(curr)

    n = len(permutation) - 2
    position    = [-1 for i in range(0, n+2)]
    #sign        = [-1 for i in range(0, n+2)]


    for i in range(1, n+2) :
        position[abs(permutation[i])] = i
    #    sign    [abs(permutation[i])] = permutation[i] / abs(permutation[i])

    ## 1 if the gray edge i,-(i+1) was never used.
    gray_available     = [1 for i in range(0, n+1)]
    #black_available    = [1 for i in range(0, n+1)]

    cycles = []

    for i in range(0, n+1) : 
        if gray_available[i] :
            start     = i
            cycle = [start]

            end   = start
            positive  = True
            
            while True :
                ## Will be used later, it says if after walking through
                ## the black edge we are in the right or in the left
                is_vertex_left = None

                if positive :
                    ## Gray edge: we are looking for the edge ( end,-(end+1) )
                    gray_available[end] = gray_available[end] - 1
                    end = end + 1
                    cycle.append(end)

                    ## Black edge: we are at the vertex -end.
                    if permutation[position[end]] > 0 :
                        # If the sign in that position is positive, than
                        # -end is in the left (cycle graph)                    
                        end = abs(permutation[position[end]-1])
                        is_vertex_left = False
                    
                    else :
                        # If the sign in that position is negative, than
                        # -end is in the right (cycle graph)
                        end = abs(permutation[position[end]+1])
                        is_vertex_left = True
                else :
                    ## Gray edge: we are looking for the edge ( -end, end-1  )
                    end = end - 1                                 ##  Note we swapped
                    gray_available[end] = gray_available[end] - 1 ##  these lines
                    cycle.append(end)

                    #### Black edge: we are at the vertex +end.
                    if permutation[position[end]] > 0 :
                        # If the sign in that position is positive, than
                        # +end is in the right (cycle graph)
                        end = abs(permutation[position[end]+1])
                        is_vertex_left = True
                    else : 
                        # If the sign in that position is negative, than
                        # +end is in the left (cycle graph)
                        end = abs(permutation[position[end]-1])
                        is_vertex_left = False
                        
                if end == start :
                    break
                else :
                    cycle.append(end)
                    
                    if is_vertex_left :
                        if permutation[position[end]] < 0 :
                            positive = True
                        else :
                            positive = False
                    else :                    
                        if permutation[position[end]] < 0 :
                            positive = False
                        else :
                            positive = True
            cycles.append(cycle)

    int_position = get_position(permutation)
    canonicals = []

    for cycle in cycles :
        canonicals.append(canonical_representation(cycle, int_position))

    return(canonicals, wgray, wblack)


## This main function expects three lists as input (separated by spaces):
##     (i) a comma-separated list with integer numbers. The number 0 is considered 
##          an alpha that an indel will remove. Any other number must be unique, 
##          disregarding their signs.
##    (ii) a comma-separated list of non-negative integers with one more element
##          than list in (i), it represents intergenic sizes of the input genome
##   (iii) a comma-separated list of non-negative integers, it represents intergenic
##          sizes of the target genome
##    (iv) a string with one or two capital letters of the allowed operations among the
##         following three: 
##            R for reversals only (the approx in this case is 2.5);
##            T for transpositions only (the approx in this case is 4); or
##            RT for reversals and transpositions (the approx in this case is 4).

if __name__ == '__main__':
    seconds = time.time()
    permutation = eval("[%s]" % sys.argv[1])
    wblack = eval("[%s]" % sys.argv[2])
    wgray  = eval("[%s]" % sys.argv[3])
    allowed_ops = sys.argv[4]

    final_length = len(wgray)

    config, grayw, blackw = construct_str_cycle(permutation, wgray, wblack)
    sort = Intergenic_Rev(config, grayw, blackw, final_length)
    sort.sort(seconds, allowed_ops)


