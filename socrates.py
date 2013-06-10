# Aaron Mansheim, 2002


from mpc import *


def socrates_example():
	"""
	A(x) Mx -> Tx
	Ms
	=> Ts
	
	1. A(x) Mx -> Tx
	2. Ms			=> Ts
	3. Ms -> Ts		1 UI
	4. Ts			2,3 MP
	"""
	x = Var('x')
	s = Var('s')

	supplied_premise = [
	
		# All men (M) are mortal (T)
		MPCProposition((Quant(forall, x), (('M1', x), impl, ('T1', x)))), # 0
		
		# Socrates (s) is a man
		MPCProposition(('M1', s)) # 1
	]
	# conclusion: Socrates is mortal
	# MPCProposition(('T1', s))
	
	Ms_then_Ts = supplied_premise[0].UI(s)
	Ts = Ms_then_Ts.MP(supplied_premise[1])
	
	return Ts
	
print 'socrates_example', socrates_example()