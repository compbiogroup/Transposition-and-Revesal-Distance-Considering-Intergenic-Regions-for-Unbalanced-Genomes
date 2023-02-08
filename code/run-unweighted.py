import sys
import os

operations = [0.1, 0.3, 0.5, 1]
qtd = 1000

os.system("mkdir -p output-unweighted")

# for n in range(50, 501, 50):
# 	for op in operations:
# 		for model in ["T"]:
# 			fileinput = "Instances/input/%s_%s_%s.in" % (model.lower(), n, op)
# 			output = "output-unweighted/%s_%s_%s.out" % (model.lower(), n, op)

# 			with open(fileinput) as file:
# 				for line in file:
# 					pi, bpi, biota = line.split()

# 					command = "python3 unweighted/r-t-rt-indel-intergenic.py %s %s %s %s >> %s" % (pi, bpi, biota, model, output)
# 					print(command)
# 					os.system(command)

for n in range(50, 501, 50):
	for op in operations:
		for model in ["RT"]:
			fileinput = "Instances/input/%s_%s_%s.in" % ("s"+model.lower(), n, op)
			output = "output-unweighted/%s_%s_%s.out" % ("s"+model.lower(), n, op)

			with open(fileinput) as file:
				for line in file:
					pi, bpi, biota = line.split()

					command = "python3 unweighted/r-t-rt-indel-intergenic.py %s %s %s %s >> %s" % (pi, bpi, biota, model, output)
					print(command)
					os.system(command)
