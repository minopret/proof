# Aaron Mansheim, 2002


from proof import *

# Let's show off the proof system! The following examples demonstrate
# how to represent proofs in this system. They also serve as a regression test.



# Example of several inference rules

def exercises_2_4_2_problem_7():
	supplied_premise = (
		Proposition((P, impl, (R, impl, (neg, S)))),	# 0
		Proposition((((neg, U), impl, V), disj, T)),	# 1
		Proposition(((neg, U), disj, R)),		# 2
		Proposition(((X, conj, P), conj, (neg, T))),	# 3
	)
	(x_and_p, not_t)	= supplied_premise[3]	.Simp()
	not_u_then_v		= supplied_premise[1]	.DS(not_t)
	(x, p)			= x_and_p		.Simp()
	r_then_not_s		= supplied_premise[0]	.MP(p)
	conjoined_conditional	= not_u_then_v		.Conj(r_then_not_s)
	v_or_not_s		= conjoined_conditional	.Dilm(supplied_premise[2])
	
	return v_or_not_s



# Example of conditional proof: proof of tautology "A -> A"

def a_then_a_by_CP():
	def anything_proves_itself(p):
		"From a statement, prove the same statement."
		return p

	a_then_a = CP(anything_proves_itself)(Proposition(A))
	return a_then_a

# Example of conditional and indirect proof: proof of tautology "A -> ~~A",
# without using the double negation equivalence.

def a_then_not_not_a_by_CP_and_IP():
	def a_proves_not_not_a_by_IP(assumption):
		def anything_proves_its_conjunction_with_assumption(prop):
			return assumption.Conj(prop)
		not_not_a = IP(anything_proves_its_conjunction_with_assumption)(Proposition((neg, A)))
		return not_not_a
	a_then_not_not_a = CP(a_proves_not_not_a_by_IP)(Proposition(A))
	return a_then_not_not_a



# Examples of proof using equivalence rules with inference rules,
# but without conditional or indirect proof.

def exercises_2_4_3_problem_2():
	supplied_premise = (
		Proposition((neg, ((neg, T), disj, (neg, U)))),	# 0
		Proposition((neg, (V, iff, T))),		# 1
		Proposition(((neg, V), iff, X))			# 2
	)
	not_not_t_and_not_not_u	= supplied_premise[0]		.DeME()
	t_and_not_not_u		= not_not_t_and_not_not_u	.DNE([0])
	(t, not_not_u)		= t_and_not_not_u		.Simp()
	t_not_iff_v		= supplied_premise[1]		.ComE([1])
	t_iff_not_v		= t_not_iff_v			.NBE()
	not_v			= t_iff_not_v			.BMP(t)
	x			= supplied_premise[2]		.BMP(not_v)
	
	return x

def exercises_2_4_3_problem_7():
	supplied_premise = (
		Proposition((W, impl, X)),				# 0
		Proposition(((W, impl, Y), impl, (Z, disj, X))),	# 1
		Proposition(((W, conj, X), impl, Y)),			# 2
		Proposition((neg, Z))					# 3
	)
	x_and_w_then_y		= supplied_premise[2]		.ComE([0])
	x_then_w_then_y		= x_and_w_then_y		.ExpE()
	w_then_w_then_y		= supplied_premise[0]		.HS(x_then_w_then_y)
	w_and_w_then_y		= w_then_w_then_y		.ExpE()
	w_then_y		= w_and_w_then_y		.TauE([0])
	z_or_x			= supplied_premise[1]		.MP(w_then_y)
	x			= z_or_x			.DS(supplied_premise[3])
	
	return x

def exercises_2_4_3_problem_8():
	supplied_premise = (
		Proposition((I, impl, J)),				# 0
		Proposition((I, disj, ((neg, (neg, K)), conj, (neg, (neg, J))))), # 1
		Proposition((L, impl, (neg, K))),			# 2
		Proposition((neg, (I, conj, J)))			# 3
	)
	i_or_k_and_not_not_j	= supplied_premise[1]		.DNE([2, 0])
	i_or_k_and_j		= i_or_k_and_not_not_j		.DNE([2, 2])
	i_or_k_and_i_or_j	= i_or_k_and_j			.DstE()
	(i_or_k, i_or_j)	= i_or_k_and_i_or_j		.Simp()
	not_i_or_not_j		= supplied_premise[3]		.DeME()
	i_then_not_j		= not_i_or_not_j		.ConE()
	not_not_k_then_not_l	= supplied_premise[2]		.TrnE()
	k_then_not_l		= not_not_k_then_not_l		.DNE([0])
	i_then_not_j_and_k_then_not_l	= i_then_not_j		.Conj(k_then_not_l)
	not_j_or_not_l		= i_then_not_j_and_k_then_not_l	.Dilm(i_or_k)
	not_l_or_not_j		= not_j_or_not_l		.ComE()
	
	return not_l_or_not_j

def exercises_2_4_4_problem_10():
	supplied_premise = (
		Proposition((A, iff, I)),
		Proposition(((neg, I), impl, (neg, Y))),
		Proposition(((neg, Y), impl, Y))
	) # conclude Proposition((A, iff, Y))
	
	y_then_i		= supplied_premise[1]		.TrnE()
	a_then_i_and_i_then_a	= supplied_premise[0]		.BicE()
	(a_then_i, i_then_a)	= a_then_i_and_i_then_a		.Simp()
	y_then_a		= y_then_i			.HS(i_then_a)
	
	def not_y_then_not_a_by_CP(not_y):
		y		= supplied_premise[2]		.MP(not_y)
		y_and_not_y	= y				.Conj(not_y)
		y_and_not_y_or_not_a	= y_and_not_y		.Add()(Proposition((neg, A)))
		dn_y_and_not_y_or_not_a	= y_and_not_y_or_not_a	.DNE([0])
		not_y_nor_not_not_y_or_not_a	= dn_y_and_not_y_or_not_a	.DeME([0, 1])
		not_y_or_not_not_y_then_not_a	= not_y_nor_not_not_y_or_not_a	.ConE()
		not_y_or_not_not_y	= not_y			.Add()(Proposition((neg, (neg, Y))))
		not_a		= not_y_or_not_not_y_then_not_a	.MP(not_y_or_not_not_y)
		
		return not_a
	
	not_y_then_not_a	= CP(not_y_then_not_a_by_CP)(Proposition((neg, Y)))
	a_then_y		= not_y_then_not_a		.TrnE()
	
	a_then_y_and_y_then_a	= a_then_y			.Conj(y_then_a)
	a_iff_y			= a_then_y_and_y_then_a		.BicE()
	
	return a_iff_y

print 'exercises_2_4_2_problem_7', exercises_2_4_2_problem_7()
print 'a_then_a_by_CP', a_then_a_by_CP()
print 'a_then_not_not_a_by_CP_and_IP', a_then_not_not_a_by_CP_and_IP()
print 'exercises_2_4_3_problem_2', exercises_2_4_3_problem_2()
print 'exercises_2_4_3_problem_7', exercises_2_4_3_problem_7()
print 'exercises_2_4_3_problem_8', exercises_2_4_3_problem_8()
print 'exercises_2_4_4_problem_10', exercises_2_4_4_problem_10()