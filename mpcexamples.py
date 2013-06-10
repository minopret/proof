# Aaron Mansheim, 2002


from mpc import *


def exercises_2_4_2_problem_7():
	supplied_premise = (
		MPCProposition((P, impl, (R, impl, (neg, S)))),	# 0
		MPCProposition((((neg, U), impl, V), disj, T)),	# 1
		MPCProposition(((neg, U), disj, R)),		# 2
		MPCProposition(((X, conj, P), conj, (neg, T))),	# 3
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

	a_then_a = CP(anything_proves_itself)(MPCProposition(A))
	return a_then_a

# Example of conditional and indirect proof: proof of tautology "A -> ~~A",
# without using the double negation equivalence.

def a_then_not_not_a_by_CP_and_IP():
	def a_proves_not_not_a_by_IP(assumption):
		def anything_proves_its_conjunction_with_assumption(prop):
			return assumption.Conj(prop)
		not_not_a = IP(anything_proves_its_conjunction_with_assumption)(MPCProposition((neg, A)))
		return not_not_a
	a_then_not_not_a = CP(a_proves_not_not_a_by_IP)(MPCProposition(A))
	return a_then_not_not_a


# Examples of proof using equivalence rules with inference rules,
# but without conditional or indirect proof.

def exercises_2_4_3_problem_2():
	supplied_premise = (
		MPCProposition((neg, ((neg, T), disj, (neg, U)))),	# 0
		MPCProposition((neg, (V, iff, T))),			# 1
		MPCProposition(((neg, V), iff, X))			# 2
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
		MPCProposition((W, impl, X)),				# 0
		MPCProposition(((W, impl, Y), impl, (Z, disj, X))),	# 1
		MPCProposition(((W, conj, X), impl, Y)),		# 2
		MPCProposition((neg, Z))				# 3
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
		MPCProposition((I, impl, J)),				# 0
		MPCProposition((I, disj, ((neg, (neg, K)), conj, (neg, (neg, J))))), # 1
		MPCProposition((L, impl, (neg, K))),			# 2
		MPCProposition((neg, (I, conj, J)))			# 3
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
		MPCProposition((A, iff, I)),
		MPCProposition(((neg, I), impl, (neg, Y))),
		MPCProposition(((neg, Y), impl, Y))
	) # conclude MPCProposition((A, iff, Y))
	
	y_then_i		= supplied_premise[1]		.TrnE()
	a_then_i_and_i_then_a	= supplied_premise[0]		.BicE()
	(a_then_i, i_then_a)	= a_then_i_and_i_then_a		.Simp()
	y_then_a		= y_then_i			.HS(i_then_a)
	
	def not_y_then_not_a_by_CP(not_y):
		y		= supplied_premise[2]		.MP(not_y)
		y_and_not_y	= y				.Conj(not_y)
		y_and_not_y_or_not_a	= y_and_not_y		.Add()(MPCProposition((neg, A)))
		dn_y_and_not_y_or_not_a	= y_and_not_y_or_not_a	.DNE([0])
		not_y_nor_not_not_y_or_not_a	= dn_y_and_not_y_or_not_a	.DeME([0, 1])
		not_y_or_not_not_y_then_not_a	= not_y_nor_not_not_y_or_not_a	.ConE()
		not_y_or_not_not_y	= not_y			.Add()(MPCProposition((neg, (neg, Y))))
		not_a		= not_y_or_not_not_y_then_not_a	.MP(not_y_or_not_not_y)
		
		return not_a
	
	not_y_then_not_a	= CP(not_y_then_not_a_by_CP)(MPCProposition((neg, Y)))
	a_then_y		= not_y_then_not_a		.TrnE()
	
	a_then_y_and_y_then_a	= a_then_y			.Conj(y_then_a)
	a_iff_y			= a_then_y_and_y_then_a		.BicE()
	
	return a_iff_y


def exercises_3_2_1_problem_7(): # may use UI and EG
	s = Var('s')
	x = Var('x')
	y = Var('y')
	supplied_premise = [
		MPCProposition(('B1', s)), # 0
		MPCProposition((
			(
				Quant(exists, x),
				(('G1', x), disj, ('T1', x))
			),
			impl,
			(
				Quant(forall, y),
				(('Q1', y), impl, (neg, ('G1', y)))
			)
		)), # 1
		MPCProposition((Quant(forall, x), (('B1', x), impl, ('G1', x)))) # 2
	] # therefore MPCProposition((Quant(exists, x), (neg, ('Q1', x))))
	
	Bs_then_Gs		= supplied_premise[2]	.UI(s)
	Gs			= Bs_then_Gs		.MP(supplied_premise[0])
	Gs_or_Ts		= Gs			.Add()(MPCProposition(('T1', s)))
	Ex_Gx_or_Tx		= Gs_or_Ts		.EG(s, x)
	Ay_Qy_then_not_Gy	= supplied_premise[1]	.MP(Ex_Gx_or_Tx)
	Qs_then_not_Gs		= Ay_Qy_then_not_Gy	.UI(s)
	dn_Gs_then_not_Qs	= Qs_then_not_Gs	.TrnE()
	Gs_then_not_Qs		= dn_Gs_then_not_Qs	.DNE([0])
	not_Qs			= Gs_then_not_Qs	.MP(Gs)
	Ex_not_Qx		= not_Qs		.EG(s, x)
	return Ex_not_Qx
	
def exercises_3_2_2_problem_7(): # may use QNE, QSE, BVE
	a = Var('a')
	b = Var('b')
	x = Var('x')
	y = Var('y')
	z = Var('z')
	
	supplied_premise = [
		MPCProposition((
			(Quant(exists, y), ('C1', y)),
			disj,
			(
				(Quant(exists, z), ('D1', z)),
				disj,
				(Quant(forall, x), ('E1', x))
			)
		)), # 0
		MPCProposition((
			(('G1', a), impl, (Quant(forall, x), (neg, ('C1', x)))),
			conj,
			(('H1', b), impl, (Quant(forall, x), (neg, ('D1', x))))
		)), # 1
		MPCProposition((Quant(exists, x), (neg, ('E1', x)))) # 2
	] # therefore MPCProposition((neg, (('H1', b), conj, ('G1', a))))
	
	(Ga_then_Ax_not_Cx, Hb_then_Ax_not_Dx) = supplied_premise[1]	.Simp()
	not_Ax_not_Cx_then_not_Ga	= Ga_then_Ax_not_Cx		.TrnE()
	Ex_Cx_then_not_Ga		= not_Ax_not_Cx_then_not_Ga	.QNE([0])
	Ey_Cy_then_not_Ga		= Ex_Cx_then_not_Ga		.BVE([0], y)
	not_Ax_not_Dx_then_not_Hb	= Hb_then_Ax_not_Dx		.TrnE()
	Ex_Dx_then_not_Hb		= not_Ax_not_Dx_then_not_Hb	.QNE([0])
	Ez_Dz_then_not_Hb		= Ex_Dx_then_not_Hb		.BVE([0], z)
	dn_Ex_not_Ex			= supplied_premise[2]		.DNE()
	not_Ax_Ex			= dn_Ex_not_Ex			.QNE([1])
	def elim_Ax_Ex_by_DS(Ez_Dz_or_Ax_Ex):
		Ez_Dz	= Ez_Dz_or_Ax_Ex.DS(not_Ax_Ex)
		return Ez_Dz
	Ez_Dz_or_Ax_Ex_then_Ez_Dz	= CP(elim_Ax_Ex_by_DS)(MPCProposition((
		(Quant(exists, z), ('D1', z)), disj, (Quant(forall, x), ('E1', x))
	)) )
	Ez_Dz_or_Ax_Ex_then_not_Hb	= Ez_Dz_or_Ax_Ex_then_Ez_Dz.HS(Ez_Dz_then_not_Hb)
	conjoined_conditional		= Ey_Cy_then_not_Ga.Conj(Ez_Dz_or_Ax_Ex_then_not_Hb)
	not_Ga_or_not_Hb		= conjoined_conditional.Dilm(supplied_premise[0])
	not_Hb_or_not_Ga		= not_Ga_or_not_Hb		.ComE()
	not_both_Hb_and_Ga		= not_Hb_or_not_Ga		.DeME()
	return not_both_Hb_and_Ga
	
def exercises_3_2_3_problem_7(): # may use UI and EG
	x = Var('x')
	
	supplied_premise = [
		MPCProposition((Quant(forall, x), (('P1', x), impl, ('A1', x))))
	] # therefore:
	# MPCProposition((Quant(forall, x), ((('P1', x), conj, ('Q1', x)), impl, ('A1', x))))
	
	Px_then_Ax	= supplied_premise[0]	.UI()
	def elim_Qx_by_Simp(Px_and_Qx):
		(Px, Qx) = Px_and_Qx.Simp()
		return Px
	Px_and_Qx_then_Px	= CP(elim_Qx_by_Simp)(MPCProposition(
		(('P1', x), conj, ('Q1', x))
	) )
	Px_and_Qx_then_Ax	= Px_and_Qx_then_Px	.HS(Px_then_Ax)
	Ax_Px_and_Qx_then_Ax	= Px_and_Qx_then_Ax	.UG()
	return Ax_Px_and_Qx_then_Ax

def exercises_3_2_5_problem_7():
	# to prove:
	# (v(x)Dx -> v(y)Ey) -> (v(z)(Dz -> Ez))
	
	x = Var('x')
	y = Var('y')
	z = Var('z')
	
	def both_proves_impl(Dx_and_Ex):
		(Dx, Ex) = Dx_and_Ex.Simp()
		def truth_proves_truth(Dx):
			return Ex
		Dx_then_Ex = CP(truth_proves_truth)(Dx)
		return Dx_then_Ex
	Dx_and_Ex_then_Dx_then_Ex = CP(conj_proves_impl)(
		MPCProposition((('D1', x), conj, ('E1', x)))
	)
	
	def false_antecedent_proves_impl(not_Dx):
		not_Dx_or_Ex	= not_Dx.Add()(MPCProposition(('E1', x)))
		Dx_then_Ex	= not_Dx_or_Ex.ConE()
		return Dx_then_Ex
	not_Dx_then_Dx_then_Ex = CP(neither_proves_impl)(
		MPCProposition(((neg, ('D1', x)), conj, (neg, ('E1', x))))
	)
	
	def conj_proves_left(A_and_B):
		(A, B) = A_and_B.Simp()
		return A
	not_Dx_and_not_Ex_then_not_Dx = CP(conj_proves_left)(
		MPCProposition(((neg, ('D1', x)), conj, (neg, ('E1', x))))
	)
	not_Dx_and_Ex_then_not_Dx = CP(conj_proves_left)(
		MPCProposition(((neg, ('D1', x)), conj, ('E1', x)))
	)
	not_Dx_and_not_Ex_then_Dx_then_Ex = not_Dx_and_not_Ex_then_not_Dx.HS(not_Dx_then_Dx_then_Ex)
	not_Dx_and_Ex_then_Dx_then_Ex = not_Dx_and_Ex_then_not_Dx.HS(not_Dx_then_Dx_then_Ex)

###	
	
def do_not_test():
	print 'exercises_2_4_2_problem_7', exercises_2_4_2_problem_7()
	print 'a_then_a_by_CP', a_then_a_by_CP()
	print 'a_then_not_not_a_by_CP_and_IP', a_then_not_not_a_by_CP_and_IP()
	print 'exercises_2_4_3_problem_2', exercises_2_4_3_problem_2()
	print 'exercises_2_4_3_problem_7', exercises_2_4_3_problem_7()
	print 'exercises_2_4_3_problem_8', exercises_2_4_3_problem_8()
	print 'exercises_2_4_4_problem_10', exercises_2_4_4_problem_10()
	print 'exercises_3_2_1_problem_7', exercises_3_2_1_problem_7()

	x = Var('x')
	y = Var('y')
	z = Var('z')
	p = MPCProposition((neg, (Quant(forall, x), (neg, (A, conj, ('P1', y))))))
	q = MPCProposition((Quant(forall, x), (('P1', x), impl, A)))
	r = MPCProposition((Quant(exists, x), ('M1', x)))
	s = MPCProposition((Quant(forall, x), (('M1', x), impl, ('V1', x))))
	print 'p', p
	print 'p.QNE', p.QNE()
	print 'q', q
	print 'q.QSE', q.QSE()
	print 'p.BVE([1], z)', p.BVE([1], z)
	print 'q.UI', q.UI()
	print 'p.EG', p.EG(y, z)
	print 'p.UG', p.UG(y, z)
	print 'r', r
	print 's', s
	def EIMP(assumption):
		conditional = s.UI()
		# consequent = conditional.MP(assumption)
		consequent = MPCProposition(('V1', x))
		conclusion = consequent.EG()
		return conclusion
	print 'r.EIMP', r.EI(EIMP)

def test():
	print 'exercises_3_2_2_problem_7', exercises_3_2_2_problem_7()
	print 'exercises_3_2_3_problem_7', exercises_3_2_3_problem_7()
	

test()