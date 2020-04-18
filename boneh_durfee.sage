# Boneh-Durfee cryptanalysis in Sagemath

# the algorithm is described in thesis of Glenn Durfee, Cryptanalysis of RSA using algebraic and lattice methods, Stanford University, 2002
# http://theory.stanford.edu/~gdurf/durfee-thesis-phd.pdf

# to run in linux terminal:
# sage /path/to/myscript.sage

# functions: ---------------------------------------

def random_between(j,k) :
	a=int(random()*(k-j+1))+j
	return a

# a simple key generation function for the testing
def key_gen(delta, bitlength):
	# set a value delta ~ 0.292
	# we generate prime numbers of bit length bitlength/2
	b = (bitlength/2)-1
	i = random_between(1,10^10)
	j = random_between(1,10^10)
	p= next_prime(1+2+2^3+i+2^b)
	q= next_prime(1+2+2^9+j+2^100+2^200+2^300+2^b)
	# we generate the modulus
	N= p*q
	phi=(p-1)*(q-1)
	# we generate a secret exponent d<N^0.3 (0.284 or even 0.292)
	d=0
	for i in range(100):
		d1=ZZ.random_element(N^(delta))
		if gcd(d1,phi)==1 and d1<N^(delta):
			d=d1
			break
	# we generate the public exponent e, and we check whether e~N
	if gcd(d,phi)==1:
		e=int(mod(d^(-1),phi))
	else:
		print false
	# the upper bounds (X,Y)=(e^delta,e^.5)
	X=floor(e^delta);Y=floor(e^.5)
	return p,q,N,phi,d,e,X,Y

# we define the x-shift polynomials
def xshift(k,i):
	return ((x*X)^i)*(f^k)
	
# we define the y-shift polynomials
def yshift(k,j):
	return ((y*Y)^j)*(f^k)

# creating the Boneh-Durfee lattice
def BD_lattice(m,t):
	xlat=[]
	for l in range(0,m+1):
		for k in range(0,l+1):
			xlat.append(xshift(k,l-k))
	ylat=[]
	for j in range(1,t+1):
		for k in range(0,m+1):
			ylat.append(yshift(k,j))
	# adjoin the two arrays xlat and ylat in one:
	lat=xlat+ylat
	# make the list lat into an array:
	# import numpy as np
	# arlat = np.asarray(lat).reshape(-1,1);
	# for example you may call a value of that array by arlat[4]

	# make an array consisting of the monomials:
	monom=[]
	for r in range(0,m+1):
		for w in range(0,r+1):
			monom.append((x^r)*(y^w))
	for w in range(1,t+1):
		for r in range(0,m+1):
			monom.append((x^r)*(y^(w+r)));

	# for each lat[], define a matrix consisting by coefficients like the one on p.65 of durfee
	coef=[[] for l in range(0,len(lat))]
	for l in range(0,len(lat)):
		for r in range(0,m+1):
			for w in range(0,r+1):
				coef[l].append(lat[l].coefficient({x:r,y:w}));
	for l in range(0,len(lat)):
		for w in range(1,t+1):
			for r in range(0,m+1):
				coef[l].append(lat[l].coefficient({x:r,y:w+r}));
	# the matrix now is ready
	L=matrix(QQ,coef)

	return lat, L, monom
	
# a function for transforming rows to polynomials
def rows2poly(mat,row, monom):
	return sum(mat[row][i]*monom[i]/monom[i].subs(x=X,y=Y) for i in range(mat.dimensions()[1]))

# a cryptanalysis function that returns the private key
def d_recovery(H,N,e):
	K.<y>=QQ[]
	H1=K(H)
	root=H1.roots()
	
	phi1=N+1-root[0][0]
	p1=((N+1-phi1)+sqrt(abs(N+1-phi1)^2-4*N))/2
	q1=((N+1-phi1)-sqrt(abs(N+1-phi1)^2-4*N))/2
	Z=ZZ
	phi11=Z(phi1)
	e1=Z(e)
	d1=int(mod((e1)^(-1),phi1))

	return d1

# main: --------------------------------------------

print '----------------------------------------------'
print '----- Testing the Boneh-Durfee algorithm -----'
print '----------------------------------------------'
print 'Bugs: 1) for RSA modulus of 2048 bits or greater,\n\td1=ZZ.random_element(N^(delta))\n\tOverflowError: cannot convert float infinity to integer'
print '----------------------------------------------'
print '----------------------------------------------'

bl = input('Enter the RSA modulus bit length: ')
# note that for 2048-RSA: 'OverflowError: cannot convert float infinity to integer'
# for 1024 bits, works fine
delta = input('Input the delta parameter (should be at most 0.292): ')
m = input('Input the parameter m for the lattice: ')
t = input('Input the parameter t for the lattice: ')

# set a value for delta (at most 0.292) for input - for instance delta = 0.274
(p,q,N,phi,d,e,X,Y) = key_gen(delta,bl)

print '\nThe generated public key pair:'
print 'N = ', N
print 'e = ', e

print '\nThe generated private key:'
print 'd = ', d

# setting up the bivariate polynomial
R.<x,y>=QQ[]
f=(-(N+1)*x+x*y-1)/e;
f=f(x=x*X,y=y*Y)

# input m,t for the parameters defining the size of the lattice
lat, L, monom = BD_lattice(m,t)

# we use the LLL algorithm on the Boneh-Durfee matrix
Lred=L.LLL()

# create a list of all polynomials from the lattice
h=[]
for i in range(0,len(lat)):
	h.append(rows2poly(Lred,i, monom))

# the candidate root we are looking for
x0 = (e*d-1)/phi
y0 = (p+q)

print '\nCandidate root:\n\tx0 = (e*d-1)/phi\n\ty0 = (p+q)'
print 'Evaluating the lattice polynomials at (x0,y0):'
# checking for which polynomials of the reduced matrix, (x0,y0) is a root
for i in range(0,len(lat)):
	#print("For polynomial {} : {}".format(i+1, h[i](x0,y0).n())) 
	print 'For polynomial', i+1 , ':',  h[i](x0,y0).n()

# for two polynomials in the lattice
# get the resultant to see if they are algebraically independent
# and measure the resultant time consumption
print '\nCalculating time (in sec) for resultant computation:'
time H=h[0].resultant(h[1])
# we want the degree to be >0
# print(H.degree())
print '\nThe degree of the resultant is', H.degree()

if H.degree()>0 and h[1](x0,y0).n()==0:
	d1 = d_recovery(H,N,e)
	if d == d1:
		print 'Key is recovered'
		#print('Key is recovered')
else:
	print 'Key not recovered'
