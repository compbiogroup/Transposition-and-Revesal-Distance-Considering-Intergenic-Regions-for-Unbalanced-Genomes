import numpy as np
import sys

def next(pi, index):
    if index == len(pi)-1:
        return None
    return abs(pi[index + 1])

def previous(pi, index):
    if index == 0:
        return None
    return abs(pi[index - 1])

instances = int(sys.argv[1])
size = int(sys.argv[2])
number_op = int(sys.argv[3])
operations = sys.argv[4]
signed = 0

if sys.argv[4] == "srt":
    operations = list("rt")
    signed = 1
if operations == "sr":
    operations = list("r")
    signed = 1

operations = list(operations)

seed = 1501

np.random.seed(seed)

min_size = 0
max_size = 100

for _ in range(instances):
    pi = list(range(1,size + 1))
    breve_iota = list()

    for _ in range(size + 1):
        breve_iota.append(np.random.randint(min_size, max_size+1))    

    breve_pi = [x for x in breve_iota]

    for _ in range(int(number_op/3)):
        op = np.random.choice(operations)
        if op == "r":
            i = np.random.randint(0, len(pi))
            j = np.random.randint(min(len(pi)-1,i+1), len(pi))
            x = np.random.randint(0, max(1, breve_pi[i]))
            y = np.random.randint(0, max(1, breve_pi[j+1]))
            x_prime = breve_pi[i] - x
            y_prime = breve_pi[j+1] - y

            segment = pi[i:j+1]
            segment.reverse()
            if signed == 1:
                #change signs in case of signed strings
                for index in range(len(segment)):
                    segment[index] = -segment[index]

            segment_breve = breve_pi[i+1:j+1]#segment from i+1 to j
            segment_breve.reverse()

            pi = pi[0:i] + segment + pi[j+1:len(pi)+1]
            # print("pi",pi)

            breve_pi[i] = x + y
            breve_pi[j+1] = x_prime + y_prime
            breve_pi = breve_pi[0:i+1] + segment_breve + breve_pi[j+1:len(breve_pi)+1]
        else:
            i = np.random.randint(0, len(pi)-1)
            j = np.random.randint(min(len(pi)-1,i+1), len(pi))
            k = np.random.randint(min(len(pi),j+1), len(pi)+1)
            x = np.random.randint(0, max(1, breve_pi[i]))
            y = np.random.randint(0, max(1, breve_pi[j]))
            z = np.random.randint(0, max(1, breve_pi[k]))            
            x_prime = breve_pi[i] - x
            y_prime = breve_pi[j] - y
            z_prime = breve_pi[k] - z

            pi = pi[0:i] + pi[j:k] + pi[i:j] + pi[k:len(pi)]
            breve_pi = breve_pi[0:i] + [x + y_prime] + breve_pi[j+1:k] + [z + x_prime] + breve_pi[i+1:j] + [y + z_prime] + breve_pi[k+1:len(breve_pi)]

    for _ in range(int(number_op/3)):
        index = np.random.randint(0, len(pi))
        x = np.random.randint(0, max(1,breve_pi[index]))
        y = np.random.randint(0, max(1,breve_pi[index+1]))
        # print(index, x, y)
        if (pi[index]-1 in [abs(x) for x in pi]) and (pi[index]+1 in [abs(x) for x in pi]):
            y_prime = breve_pi[index+1] - y
            pi = pi[0:index] + pi[index+1:len(pi)+1]
            breve_pi = breve_pi[0:index] + [x + y_prime] + breve_pi[index+2:len(breve_pi)+1]

    for _ in range(int(number_op/3)):
        pre = np.random.randint(min_size, max_size+1)
        post = np.random.randint(min_size, max_size+1)
        index = np.random.randint(0, len(pi))
        x = np.random.randint(0, max(1,breve_pi[index]))
        x_prime = breve_pi[index] - x
        if (previous(pi, index) != 0 and pi[index] != 0):
            pi = pi[0:index] + [0] + pi[index:len(pi)+1]
            breve_pi[index] = x + pre
            breve_pi = breve_pi[0:index+1] + [x_prime + post] + breve_pi[index+1:len(breve_pi)+1]

    # print(pi)
    #check instance
    if(len(pi)+1 != len(breve_pi)):
        print("Size error", len(pi), len(breve_pi))
        exit()
    
    abs_pi = [abs(x) for x in pi]
    for i in range(1, size, 2):
        if i not in abs_pi and i+1 not in abs_pi:
            print("insertion error")
            exit()

    for i in range(len(pi)-1):
        if pi[i] == 0 and pi[i+1] == 0:
            print("deletion error")
            print(pi)
            exit()

    str_pi = ",".join([str(x) for x in pi])
    str_breve_pi = ",".join([str(x) for x in breve_pi])
    str_breve_iota = ",".join([str(x) for x in breve_iota])

    print(str_pi, str_breve_pi, str_breve_iota)
