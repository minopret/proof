import sys
import types

assert sys.version_info >= (2, 2)

# Implementation of a proof verification system
# for propositional logic.
#
# Aaron Mansheim
# April 2002
#
# INTRODUCTION
#
# In its relatively brief history, computer science has provided a whole
# new approach to the age-old foundations of mathematics. Mathematics, on
# the other hand, is what makes computer science scientific. The two
# fields are closely related in many ways. One key relationship between
# the two fields is in proof theory. Modern mathematics is based on
# proofs. Proofs tell us how to use standard rules of inference to turn
# something that we know into something that we want to know. The process
# of inference is computational. If we describe the steps of a proof
# formally enough, we can make a computer program that follows each step
# to produce the logical result.
# 
# A system for describing proofs this formally can be useful. It requires
# us to write proofs without relying on anyone else to supply necessary
# details. It makes manifest that anyone who follows the necessary steps,
# even a computer, will reach the logical result.
# 
# GOALS
# 
# 1. To create a computer system in which we can implement logical
# constructions as programs. That is, each program will represent a proof
# in propositional logic. Running the program will cause the system to
# perform a verification of the proof.
# 
# 2. To use a simple programming language (a subset of Python) to
# implement this system. Those who know other programming languages,
# but not Python, can be assured that the simple parts are easy to read,
# and the hard parts are few.
# 
# Note: We are now discussing two programming environments. The first one is
# the Python-like language that we use to build a logic system. The second
# is the logic system itself, which can be used to process proofs. These
# two environments are related, but we need to be aware they are distinct.
# 
# 3. To make the system itself very small.
#
# FUTURE PLANS
#
# 1. A successful proof will produce a new global symbol that
#    implements the inference rule that the proof justifies.
#    In Python, this means dynamically constructing and evaluating
#    a lambda expression. Built-in inference rules will be present
#    without proof, but any additional inference rule (theorem)
#    will become available for use only when its proof is verified.
#
# 2. Interpret strings as statements, so that a formula can be typed
#    in, for example, as 'P -> (R -> ~S)'. Of course it should be
#    printed in the same form. Note that typographic characters for
#    the standard logic symbols are available in recent computing systems
#    and software, via Unicode.
#
#
# WORKS CONSULTED
#
# Harlan Miller. Modern Logic and its Development.
# 	Blacksburg Va., Kinko's Copy Center, Fall 1991 (PHIL 3505 #1)
#
# Source of the WFF rules, inference rules, and equivalence rules.
#
#
# WORKS NOT CONSULTED
#
# Robert Boyer. A Computational Logic.
#
# I am not the first to implement a computational logic system.
# I have not read this book, but it's where I would go
# for the full story on computational logic systems.
#
# Stuart Shapiro. Common Lisp: An Interactive Approach.
#
# Exercises involve match and bind functions to implement the classic
# Eliza program. But don't blame him for my match and bind functions.



# First, definitions that make sure that certain variables evaluate to
# distinct values. They help us to define formulas somewhat compactly.
# For example, "if P, then if R, then not S", meaning
# "P implies the statement that R implies the negation of S",
# can be typed as
#	[P, impl, [R, impl, [neg, S]]]
# which evaluates to the slightly less compact form
#	['P', '->', ['R', '->', ['~', 'S']]]
# It is often convenient to name variables in a way that suggests
# their contents. Example:
#	p_then_r_then_not_s = [P, impl, [R, impl, [neg, S]]]
# Of course, the name of a variable is only a mnemonic.
# We would use the same words to write the statements themselves,
# but the words "and", "or", "not", and "then" already mean something
# to Python.
#
# Summary:
# operator name: 	not, or, and, then, iff
# definition form:	neg, disj, conj, impl, iff
# stored/printed form:	'~', 'v', '&', '->', '<->' 

neg = '~';
conj = '&';
disj = 'v';
impl = '->';
iff = '<->';

A = 'A'; B = 'B'; C = 'C'; D = 'D'; E = 'E'; F = 'F'; G = 'G'; H = 'H'; I = 'I';
J = 'J'; K = 'K'; L = 'L'; M = 'M'; N = 'N'; O = 'O'; P = 'P'; Q = 'Q'; R = 'R';
S = 'S'; T = 'T'; U = 'U'; V = 'V'; W = 'W'; X = 'X'; Y = 'Y'; Z = 'Z';
	
	
	
# Before we go any further, let's recognize that correct logic
# implies the existence of incorrect logic.

class LogicException(Exception):
	pass



# Second, definitions of a well-formed formula (WFF) of our propositional logic.
# Note that the return values '1' and '0' mean 'true' and 'false' as usual.

def _is_well_formed(l):
	"""
	Checks whether the list 'l' represents
	a well-formed formula (WFF) of our propositional logic.
	"""
	if _is_symbol(l):
		return 1
	if (type(l) == types.TupleType and len(l) == 2
			and l[0] == neg and _is_well_formed(l[1])):
		return 1
	if (type(l) == types.TupleType and len(l) == 3
			and _is_binary(l[1])
			and _is_well_formed(l[0]) and _is_well_formed(l[2])):
		return 1
	return 0

def _is_symbol(s):
	"""
	Checks whether the string 's' represents a symbol
	of our propositional logic, that is, a variable that may
	itself stand for a true or false statement (a proposition).
	Any string that starts with a capital letter is a symbol.
	"""
	if (type(s) == types.StringType and s >= 'A' and s[0] <= 'Z'
			and (len(s) < 2 or s[1] < '0' or s[1] > '9')):
		return 1
	return 0

def _is_binary(s):
	"""
	Checks whether the string 's' represents a binary operator
	of our propositional logic.
	"""
	if (type(s) == types.StringType
			and (s == conj or s == disj or s == impl or s == iff)):
		return 1
	return 0


# Next, the main and only mechanism that we need in order to implement
# logical inference rules in Python.

def _match(l, m):
	"""
	Matches the logical formula 'm' with the logical formula 'l',
	and reports the interpretations of variables of 'l'
	as subexpressions of 'm', in the form of a dictionary object.
	
	Multiple occurrences of one symbol are allowed to
	have different or even incompatible interpretations.
	Only the last interpretation is reported.
	
	Example:
	_match([A, conj, A], [[neg, B], conj, B]) == {A: B}
	"""
	if _is_symbol(l):
		return {l[0]: m}
	elif len(l) == 2 and l[0] == neg and len(m) == 2 and m[0] == neg:
		return _match(l[1], m[1])
	elif len(l) == 3 and _is_binary(l[1]) and len(m) == 3 and m[1] == l[1]:
		return dict(_match(l[0],m[0]).items() + _match(l[2],m[2]).items())
	else:
		raise LogicException()
	



# Some additional mechanisms are necessary for equivalence rules.
# We need to work on parts of expressions. And some of the rules
# need to repeat a symbol in the left-hand side of a rewrite.

def _strict_match(l, m):
	"""
	Matches the logical formula 'm' with the logical formula 'l',
	and reports the interpretations of variables of 'l'
	as subexpressions of 'm', in the form of a dictionary object.
	
	Multiple occurrences of one symbol are NOT allowed to
	have different interpretations.
	
	Examples:
	_strict_match([A, conj, A], [[neg, B], conj, [neg, B]]) == {A: [neg, B]}
	_strict_match([A, conj, A], [B, conj, [neg, B]]) # raises LogicException
	"""
	if _is_symbol(l):
		return {l[0]: m}
	elif len(l) == 2 and l[0] == neg and len(m) == 2 and m[0] == neg:
		return _strict_match(l[1], m[1])
	elif len(l) == 3 and _is_binary(l[1]) and len(m) == 3 and m[1] == l[1]:
		m1 = _strict_match(l[0],m[0])
		m2 = _strict_match(l[2],m[2])
		m = dict(m1.items() + m2.items())
		
		# Common keys must have equal values.
		# Better algorithm?
		for symbol in m1.keys():
			if m1[symbol] != m[symbol]:
				raise LogicException()
		return m
	else:
		raise LogicException()

# Assumes immutable input
def _bind(interp, formula):
	if _is_symbol(formula):
		if interp.has_key(formula):
			return interp[formula]
		return formula
	elif formula == '~' or _is_binary(formula):
		return formula
	result = map(lambda x:_bind(interp, x), formula)
	return tuple(result)

# This is NOT an in-place operation. Assumes immutable input.
def _replace_match_at(formula, position_list, rule_list):
	ancestry = []
	parent = formula
	parent_pos = None
	subexpression = formula
	for pos in position_list:
		parent = subexpression
		parent_pos = pos
		ancestry.append([parent, parent_pos])
		subexpression = parent[parent_pos]
	
	interp = None
	new_pattern = None
	for rule in rule_list:
		if len(rule) == 3 and rule[2] == 1:
			try:
				interp = _strict_match(rule[0], subexpression)
				new_pattern = rule[1]
				break
			except LogicException:
				pass
		else:
			try:
				interp = _match(rule[0], subexpression)
				new_pattern = rule[1]
				break
			except LogicException:
				pass
	if interp == None:
		raise LogicException()
	formula = _bind(interp, new_pattern)
	
	ancestry.reverse()
	for ancestor in ancestry:
		child = formula
		formula = list(ancestor[0])
		formula[ancestor[1]] = child
		formula = tuple(formula) # for immutable output
	return formula


# Having defined the parts of a proposition,
# and the operations on the parts of a proposition,
# we're ready to define a proposition.
#
# The form of a proposition is verified when it is
# created, and it carries its class membership as
# proof of well-formedness.

def checked_proposition(object):
	if not isinstance(object, Proposition):
		raise TypeError()
	return object

class Proposition:
	"""
	A logical proposition compounded of individual, undefined statements.
	
	A list whose constructor verifies the form of the list.
	"""

	# It is somewhat wasteful for this to be the only way to create a proposition.
	# Even propositions created in member functions are checked for form.
	
	def __init__(self, l):
		"Creates a new proposition of the specified form."
		if not _is_well_formed(l):
			raise TypeError()
		self.data = l
	
	# def __init__(self, s) # future
	
	def __cmp__(self, other):
		return cmp(self.data, other)
	
	def __len__(self):
		return len(self.data)
	
	def __getitem__(self, key):
		
		# I don't like this, but it's what the
		# language reference manual calls for.
		
		if type(key) == types.SliceType:
			(s, t, p) = (key.start, key.stop, key.step)
			assert p == None
			if s == None:
				if t == None:
					return self[:]
				else:
					return self.data[:t]
			else:
				if t == None:
					return self.data[s:]
				else:
					return self.data[s:t]
		return self.data[key]
	
	def __str__(self): # opportunity for future enhancement
		return str(self.data)



	# Now, a group of inference rules for "natural deduction"
	# in propositional logic.
	
	def modus_ponens(self, left_side):
		"""
		Proposition([A, impl, B]).MP(Proposition(A))
			== Proposition(B)
		
		A
		A -> B
		=>
		B
		"""
		checked_proposition(left_side)
		interp = _match((A, impl, B), self)
		if interp[A] == left_side:
			return self.__class__(interp[B])
		raise LogicException()
	MP = modus_ponens

	def modus_tollens(self, neg_right_side):
		"""
		Proposition([A, impl, B]).MT(Proposition([neg, B]))
			== Proposition([neg, A])
		
		~B
		A -> B
		=>
		~A
		"""
		checked_proposition(neg_right_side)
		interp = _match([A, impl, B], self)
		_match((neg, interp[B]), neg_right_side) # may raise LogicException
		return self.__class__((neg, interp[A]))
	MT = modus_tollens

	def conjunction(self, right_side):
		"""
		Proposition(A).Conj(Proposition(B))
			== Proposition([A, conj, B])
		
		A
		B
		=>
		A & B
		"""
		checked_proposition(right_side)
		return self.__class__((self[:], conj, right_side[:]))
	Conj = conjunction

	def simplification(self):
		"""
		Proposition([A, conj, B]).Simp()
			== (Proposition(A), Proposition(B))
		
		A & B
		=>
		A
		B
		"""
		interp = _match([A, conj, B], self)
		return (self.__class__(interp[A]), self.__class__(interp[B]))
	Simp = simplification

	def disjunctive_syllogism(self, neg_side):
		"""
		Proposition([A, disj, B]).DS(Proposition([neg, A]))
			== Proposition(B)
		
		A v B
		~A
		=>
		B
		
		Proposition([A, disj, B]).disjunctive_syllogism(Proposition([neg, B]))
			== Proposition(A)
		
		A v B
		~B
		=>
		A
		"""
		checked_proposition(neg_side)
		interp = _match([A, disj, B], self)
		if neg_side == (neg, interp[A]):
			return self.__class__(interp[B])
		elif neg_side == (neg, interp[B]):
			return self.__class__(interp[A])
		else:
			raise LogicException()
	DS = disjunctive_syllogism

	# We want to make a clear distinction between premises,
	# which are claimed true, from parameters, which are not.
	# It's effective, and not difficult, to make A.addition()
	# return a function that returns A v B for any B.

	def addition(self):
		"""
		Proposition(A).Add()(Proposition(B))
			== Proposition([A, disj, B])
		
		A
		=>
		A v B
		"""
		return lambda anything: self.__class__(
			(self[:], disj, checked_proposition(anything)[:])
		)
	Add = addition

	def biconditional_modus_ponens(self, one_side):
		"""
		Proposition([A, iff, B]).BMP(Proposition(A))
			== Proposition(B)
		
		A <-> B
		A
		=>
		B
		
		Proposition([A, iff, B]).biconditional_modus_ponens(Proposition(B))
			== Proposition(A)
		
		A <-> B
		B
		=>
		A
		"""
		checked_proposition(one_side)
		interp = _match((A, iff, B), self)
		if one_side == interp[A]:
			return self.__class__(interp[B])
		elif one_side == interp[B]:
			return self.__class__(interp[A])
		else:
			raise LogicException()
	BMP = biconditional_modus_ponens

	def hypothetical_syllogism(self, conditional):
		"""
		Proposition([A, impl, B]).HS(Proposition([B, impl, C]))
			== Proposition([A, impl, C]
		
		A -> B
		B -> C
		=>
		A -> C
		"""
		checked_proposition(conditional)
		interp1 = _match((A, impl, B), self)
		interp2 = _match((B, impl, C), conditional)
		if interp1[B] == interp2[B]:
			return self.__class__((interp1[A], impl, interp2[C]))
		else:
			raise LogicException()
	HS = hypothetical_syllogism

	def dilemma(self, disjunction):
		"""
		Proposition([[A, impl, B], conj, [C, impl, D]]).Dilm(
			Proposition([A, disj, C])
			)
			== Proposition([B, disj, D]
		
		(A -> B) & (C -> D)
		A v C
		=>
		B v D
		"""
		interp1 = _match(((A, impl, B), conj, (C, impl, D)), self)
		interp2 = _match((A, disj, C), disjunction)
		if interp1[A] == interp2[A] and interp1[C] == interp2[C]:
			return self.__class__((interp1[B], disj, interp1[D]))
		else:
			raise LogicException()
	Dilm = dilemma
	
	# Now, the equivalence rules.
	#
	# Notes on equivalences that are asymmetric or overloaded (that is, all of them):
	#
	# 1. They attempt each possible form and fall back to the next.
	#
	# 2. They can be implemented more efficiently as multiple partial functions.
	#    But since Python won't overload functions on either the type or the
	#    form of the arguments, this way is clearer, more concise, and more convenient.
	#
	# 3. Some of them need an additional partial function to handle a particular case.
	#       For example, the usual "~A -> ~B => B -> A", by TrnE,
	#       blocks "~A -> ~B => ~~B -> ~~A".
	#       So we have TrnE_to, which changes "A -> B" to "~B -> ~A"
	#       regardless of the forms of A and B.
	#       We could require two applications of DNE to get the same result,
	#       but that seems like an unfair hindrance to the logician.
	#       In a later version I could replace TrnE_to with its proof by TrnE and DNE.
	#
	# 4. They do not perform well for a formula represented as
	#    the empty list. However, the empty list does not represent
	#    any well-formed formula.

	def double_negation_equivalence(self, position_list=[]):
		"""
		Proposition([A, conj, [neg, [neg, B]]]).DNE([2])
			== Proposition([A, conj, B])
		
		A & ~~B <=> A & B
		
		Proposition([A, conj, [neg, [neg, B]]]).DNE([2, 1, 1])
			== Proposition([A, conj, [neg, [neg, [neg, [neg, B]]]]])
		
		A & ~~B => A & ~~~~B
		"""
		return self.__class__(_replace_match_at(self, position_list, [
			[ (neg, (neg, A)), A ],
			[ A, (neg, (neg, A)) ]
		]))
	DNE = double_negation_equivalence

	def DeMorgan_equivalence(self, position_list=[]):
		"""
		Proposition([[neg, [A, conj, B]], disj, C]).DeME([0])
			== Proposition([[neg, A], disj, [neg, B]])
		
		~(A & B) v C <=> (~A v ~B) v C
		"""
		return self.__class__(_replace_match_at(self, position_list, [
			[ ((neg, A), disj, (neg, B)), (neg, (A, conj, B)) ],
			[ (neg, (A, conj, B)), ((neg, A), disj, (neg, B)) ],
			[ ((neg, A), conj, (neg, B)), (neg, (A, disj, B)) ],
			[ (neg, (A, disj, B)), ((neg, A), conj, (neg, B)) ]
		]))
	DeME = DeMorgan_equivalence
	
	def commutation_equivalence(self, position_list=[]):
		"""
		Proposition([[A, conj, B], disj, C]).ComE([0])
			== Proposition([[B, conj, A], disj C])
		
		(A & B) v C <=> (B & A) v C
		"""
		return self.__class__(_replace_match_at(self, position_list, [
			[ (A, disj, B), (B, disj, A) ],
			[ (A, conj, B), (B, conj, A) ],
			[ (A, iff, B), (B, iff, A) ]
		]))
	ComE = commutation_equivalence
	
	def transposition_equivalence(self, position_list=[]):
		"""
		Proposition([[A, impl, B] conj, C]).TrnE([0])
			== Proposition([[[neg, B], impl, [neg, A]], conj, C])
		
		(A -> B) & C <=> (~B -> ~A) & C
		"""
		return self.__class__(_replace_match_at(self, position_list, [
			[ ((neg, B), impl, (neg, A)), (A, impl, B) ],
			[ (A, impl, B), ((neg, B), impl, (neg, A)) ]
		]))
	TrnE = transposition_equivalence
	
	def transposition_equivalence_to(self, position_list=[]):
		"""
		Proposition([[neg, B], impl, [neg, A]]).TrnE_to([])
			== Proposition([[neg, [neg, A]], impl, [neg, [neg, B]]])
		
		~B -> ~A => ~~A -> ~~B
		"""
		return self.__class__(_replace_match_at(self, position_list, [
			  (A, impl, B), ((neg, B), impl, (neg, A))
		]))
	TrnE_to = transposition_equivalence_to
	
	# Trap:
	#    Forgetting to specify the operator when attempting "A => A & A"
	#    will perform "A => A v A" instead.
	# Excuse:
	#    This is the price of having a bidirectional ComE
	#    that tries to infer the operator.
	
	def tautology_equivalence(self, position_list=[], op=disj):
		"""
		Proposition([[A, disj, A], conj, B]).ComE([0])
			== Proposition([A, conj, B])
		
		(A v A) & B <=> A & B
		
		Proposition([A, conj, B]).ComE([0], conj)
			== Proposition([[A, conj, A] conj, B])
		
		A & B => (A & A) & B
		"""
		return self.__class__(_replace_match_at(self, position_list, [
			[ (A, disj, A), A, 1 ],
			[ (A, conj, A), A, 1 ],
			[ A, (A, op, A) ]
		]))
	TauE = tautology_equivalence
	
	def distribution_equivalence(self, position_list=[]):
		return self.__class__(_replace_match_at(self, position_list, [
			[ (A, disj, (B, conj, C)), ((A, disj, B), conj, (A, disj, C)) ],
			[ (A, conj, (B, disj, C)), ((A, conj, B), disj, (A, conj, C)) ],
			[ ((A, disj, B), conj, (A, disj, C)), (A, disj, (B, conj, C)), 1 ],
			[ ((A, conj, B), disj, (A, conj, C)), (A, conj, (B, disj, C)), 1 ],
		]))
	DstE = distribution_equivalence
	
	# Also called "association"
	def regrouping_equivalence(self, position_list=[]):
		return self.__class__(_replace_match_at(self, position_list, [
			[ (A, conj, (B, conj, C)), ((A, conj, B), conj, C) ],
			[ (A, disj, (B, disj, C)), ((A, disj, B), disj, C) ],
			[ (A, iff, (B, iff, C)), ((A, iff, B), iff, C) ],
			[ ((A, conj, B), conj, C), (A, conj, (B, conj, C)) ],
			[ ((A, disj, B), disj, C), (A, disj, (B, disj, C)) ],
			[ ((A, iff, B), iff, C), (A, iff, (B, iff, C)) ]
		]))
	RgrE = regrouping_equivalence
	
	def biconditional_equivalence(self, position_list=[]):
		return self.__class__(_replace_match_at(self, position_list, [
			[ (A, iff, B), ((A, impl, B), conj, (B, impl, A)) ],
			[ ((A, impl, B), conj, (B, impl, A)), (A, iff, B), 1]
		]))
	BicE = biconditional_equivalence
	
	def conditional_equivalence(self, position_list=[]):
		return self.__class__(_replace_match_at(self, position_list, [
			[ (A, impl, B), ((neg, A), disj, B) ],
			[ ((neg, A), disj, B), (A, impl, B) ]
		]))
	ConE = conditional_equivalence
	
	def exportation_equivalence(self, position_list=[]):
		return self.__class__(_replace_match_at(self, position_list, [
			[ ((A, conj, B), impl, C), (A, impl, (B, impl, C)) ],
			[ (A, impl, (B, impl, C)), ((A, conj, B), impl, C) ]
		]))
	ExpE = exportation_equivalence
	
	def negated_biconditional_equivalence(self, position_list=[]):
		return self.__class__(_replace_match_at(self, position_list, [
			[ (neg, (A, iff, B)), (A, iff, (neg, B)) ],
			[ (A, iff, (neg, B)), (neg, (A, iff, B)) ]
		]))
	NBE = negated_biconditional_equivalence


_proposition_class = Proposition


# Last, but certainly not least, conditional and indirect proof methods.
#
# Conditional proof is another interesting case for implementation.
# We do it by taking any other rule of inference as an argument.
# It may be a built-in rule, or it may be a "proof function" that
# uses built-in rules to derive a result from one argument.
#
# This implementation depends on "deep binding" of the proof function,
# which will usually refer to symbols in its enclosing scope.
# The ability to do this is new in Python 2.2.

def conditional_proof(proof_function):
	"""
	conditional_proof(anything_proves_itself)(Proposition(A))
		== Proposition([A, impl, A])
	def anything_proves_itself(p):
		return p
	
	1. |	A	by assumption
	2. A -> A	by 1 - conditional proof
	"""

	if type(proof_function) != types.FunctionType:
		raise TypeError()
	return lambda assumption: _proposition_class(
		(checked_proposition(assumption)[:], impl, proof_function(assumption)[:])
	)
CP = conditional_proof

def indirect_proof(proof_function):
	"""
	IP(anything_proves_assumption_A_conjoined_with_it)(Proposition([neg, A]))
		== Proposition([neg, neg, A])
	assumption = A
	def anything_proves_assumption_A_conjoined_with_it(p):
		return Conj(assumption, p)
	
	1. |	A		by assumption
	2. |	|	~A	by assumption
	3. |	|	A & ~A	by 1, 2 - conjunction
	4. |	~~A		by 2 - indirect proof
	"""
	def indirect_proof_result(proof_function, assumption):
		checked_proposition(assumption)
		interp = _strict_match((A, conj, (neg, A)), proof_function(assumption))
		return _proposition_class((neg, assumption[:]))
	
	if type(proof_function) != types.FunctionType:
		raise TypeError()
	return lambda assumption: indirect_proof_result(proof_function, assumption)
IP = indirect_proof

