import sys

if len(sys.argv) < 2:
        print("Usage: python3 scaling.py <N>")
        exit()

n = int(sys.argv[1])
formula = []
nb_constraints = 0
nb_variables = 2*n

s = ""
for i in range(1,2*n+1):
	s = s + "+1 x" + str(i) + " "

s = s + " >= " + str(n+1) + " ;"
formula.append(s)

i = 1
while i < 2*n: 
	s = "-1 x" + str(i) + " -1 x" + str(i+1) + " >= -1 ;"  
	formula.append(s)
	i = i + 2

print("* #variable=" + str(nb_variables) + " #constraint=" + str(len(formula)))
for f in formula:
	print(f)
