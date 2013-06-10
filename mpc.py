# Implementation of system MPC, a monadic predicate calculus
# Aaron Mansheim
# April 2002
#
# Grammar and rules based on:
# Harlan Miller. Modern Logic and its Development.
# 	Blacksburg Va., Kinko's Copy Center, Fall 1991 (PHIL 3505 #1)
#
# Language complaint:
# The Python equivalent of a class method is simply a function.
# That would be OK, but there's no inheritance of these ersatz class methods.
# Especially, it's not possible to rely on an inherited class method to call an
# overriding class method.

from proof import *
import types

forall = conj;
exists = disj;


# Note: In system MPC, every element of a formula is a formula, except:
# 1) an operator
# 2) an application of a predicate
# 3) a quantification
# In system MPC, a formula that contains free variables is not a statement.
# This technicality will usually not affect our implementation.
# We will be comfortable matching statement constants to formulas that
# have free variables. But we will avoid matching statement constants to
# an operator, an application of a predicate, or a quantification.
#
# I can see that I might want a class "Application" to represent the
# application of a predicate to variables. That would get rid of
# the artificial naming convention to encode arity, and would help
# prevent the erroneous application of statement equivalence rules to
# individual constants and variables.
#
# I note that with classes Var, Quant, and perhaps Application,
# I have moved away from a data structure of nested lists
# whose non-list elements were exclusively strings.
# I could easily go back to that form, to show the correspondence
# to traditional Lisp programming. But I like the built-in function isinstance().



# overrides proof._is_well_formed

def _is_well_formed(l):
	"""
	Checks whether the list 'l' represents
	a well-formed formula (WFF) of our monadic predicate logic.
	"""
	if _is_statement_constant(l):
		return 1
	if len(l) == 2 and _is_quantification(l[0]) and _is_well_formed(l[1]):
		return 1
	if len(l) == 2 and _is_monadic_predicate(l[0]) and _is_individual(l[1]):
		return 1
	if len(l) == 2 and l[0] == neg and _is_well_formed(l[1]):
		return 1
	if len(l) == 3 and _is_binary(l[1]) and _is_well_formed(l[0]) and _is_well_formed(l[2]):
		return 1
	return 0

def _is_statement_constant(s):
	if (type(s) == types.StringType and s[0] >= 'A' and s[0] <= 'Z'
			and (len(s) == 1 or s[1] == '0')):
		return 1
	return 0

def _is_monadic_predicate(s):
	if (type(s) == types.StringType and s[0] >= 'A' and s[0] <= 'Z'
			and s[1] == '1'):
		return 1
	return 0

def _is_individual(s):
	return _is_individual_constant(s) or _is_individual_variable(s)

def _is_individual_constant(s):
	if type(s) == types.StringType and s[0] >= 'a' and s[0] <= 's':
		return 1
	return 0
	
def _is_individual_variable(s):
	if isinstance(s, Var):
		return 1
	return 0

def _is_quantification(s):
	if isinstance(s, Quant):
		return 1
	return 0

def _is_quantifier(s):
	return type(s) == types.StringType and s == forall or s == exists

def _is_binary(s):
	"""
	Checks whether the string 's' represents a binary operator
	of our propositional logic.
	"""
	if s == conj or s == disj or s == impl or s == iff:
		return 1
	return 0



"""
DIFFICULT EXAMPLE:
['&x', [  ['P1', 'x'],  '&',  ['&x', ['Q1', 'x']]  ]]
i.e. can a nested quantifier duplicate the variable of an enclosing quantifier?
ANSWER: yes, it can.
QUESTION: what is the interpretation of such a formula?
ANSWER: same as if the nested quantifier and the formula in its scope
used a variable different from that of the enclosing quantifier.
The variable of the nested quantifier "shadows" that of the
enclosing quantifier. That is, when the variable of the nested quantifier
has the same name as the variable of the enclosing quantifier, then
the nested quantified statement is guaranteed to be free of the variable
of the enclosing quantifier. Thus one equivalent to the above example would be:
[  ['&x', ['P1', 'x']],   '&',   ['&x', ['Q1', 'x']]  ]

HOW TO CHECK that a variable is not free in any undischarged assumption?

QUESTION: In general, when can a variable be free?
ANSWER: Not in premises. By decree, no variable is free in premises.
Not in the results of most rules.
Only in connection with five rules: UI and EI, the only rules that remove a quantifier;
and CP, IP, and addition, the only rules that introduce an arbitrary (sub)expression.
1&2) For UI and addition, only in the result: UI and addition have no inner scope.
3&4) For CP or IP, in the result.
5&6) Or again for CP or IP, in the inner scope.
7) For EI, only in the inner scope: the instantiated variable must not be free in
the conclusion, and therefore it cannot be free in the result.

QUESTION: When is a free variable available for UI?
ANSWER: Only when it can clearly bind to any individual in any model without
falsifying the proof. 1&2) In two cases, when the variable
is introduced in the result of UI or addition. 3&4) In only two other cases, when the
variable was introduced in the assumption of a CP or IP but has been exported in
the result of that CP or IP, discharging the assumption. Not in the inner scope
of a CP, IP, or EI where the variable was introduced in the assumption.
Note that free variables which have been introduced other than in the assumption
of a CP, IP, or EI can occur in its assumption. Do they shadow the outer usage?
No, but it doesn't matter. Example:

for all x, (P x & Q x) -> R x (premise)
for all x, P x (premise)
P y by UI
assume Q y
	P y & Q y by Conj
		comment: Clearly, the "y" in the assumption is NOT shadowing the outer y.
		The "y" in P y and the "y" in Q y are the same variable.
		But still we cannot use UG on this statement.
		Even if the assumption is true, it is NOT necessarily true
		that for all y, P y & Q y.
	(P y & Q y) -> R y by UI
		comment: This last IS true for all y. However, it's under suspicion because
		in a sense it COULD be contingent on the assumption (it's in the
		scope of the assumption) even though it ISN'T contingent on the assumption.
		We can just rule it ineligible for UG, for sanity's sake. We realize that if
		for some reason we needed to use UG on it, we could have taken care of the
		matter before introducing the assumption.
	R y by MP
Q y -> R y by CP
for all x, Q x -> R x by UG
		comment: This is OK because the assumption has been discharged.

In an undischarged assumption, a variable is considered to be restricted to a particular
class of individuals in the model. Specifically, it is restricted to the class
that satisfies the assumption. For EI, this class is inferred to be non-empty,
although the inference may come from an undischarged assumption that is
not necessary true. For CP or IP, it is allowable for the class to be empty.

QUESTION: Are the conditions the same for the availability of a free variable for EI?
ANSWER: Yes. When we use EI, we want to find out what is true of every individual in
a particular class, for example the class of all x for which P x is true.
If we take a variable restricted to the class of all x for which Q x is true
and then assume that P x is true, we will only find out what is true of every
individual in the intersection of classes of P x and Q y. This "might" not
be the same as the class of P x.

QUESTION: In sum, when is a free variable NOT available for EI or UG?
ANSWER: A free variable is NOT available for EG or UI when it has a free
occurrence in the assumption of any enclosing scope, meaning a
CP, IP, or EI.

QUESTION: How do we enforce that only available free variables are used
for EI or UG?
ANSWER: In one of two ways. The first way is to pass a stack of used variables up
the call chain, and check that each free variable for EI or UG is not in the stack.
Note that a level in the stack can contain more than one variable,
as it is quite possible to assume "P x & Q y".
Note also that, while programming languages naturally do manage a stack for
function calls, "shadowing" blocks an attempt to climb the call chain layer by layer.
Let's look at the other way.

The second way is to "taint" free variables in assumptions of CP, IP, and EI.
The representation of a variable should be, not a string, but an object.
Then, when an assumption is passed to the proof function for CP, IP, or EI,
The CP, IP, or EI rule should substitute a tainted copy of each free variable
object in the assumption. That is, the copy should have a property that
states that it is a free variable in an assumption. Upon the discharge of the
assumption, the conclusion will be intercepted and the variables that
were tainted will have their taint removed. For efficiency, it would also
be possible to augment every proposition with an index of the names and
positions of the tainted variables that it contains. Note that
the untainted copy can sneak in when referring to propositions in the
enclosing scope. This is a problem if we wish to stick to Dr. Miller's
rules exactly. Otherwise, the problem is not the lack of taint in such
variables, but only to ensure that they are known to be the same
variable as the corresponding tainted copy.

QUESTION: What would be the API for variable objects?
ANSWER: Our construction "Proposition(['P', 'x'])" should instead initialize a
programming language variable, as
"Proposition(['P', x = Var()])". Perhaps, on one occasion, the Python
variable x would become bound to the Var object with id 122132.
We could allow the passing of a variable name to Var() for better output,
as for example "x = Var('x')". When a variable is used only once in a
formula, usage could be simplified to "Proposition(['P', Var('x')])".
But "Proposition([['P', Var('x')], '&', ['Q', Var('x')]])"
would be an error, to be corrected as
"Proposition([['P', x = Var('x')], '&', ['Q', x]])"
The Var constructor can register each variable name, to raise a
LogicException if the same variable name is used twice to
construct Var objects.

QUESTION: Now we have a problem again: how can we reuse names of variables
which we don't mind shadowing, or whose lifetime has ended?
ANSWER: First, our logic variables are never shadowed, as shown above.
Second, we can make a __del__() method for class Var that
removes the variable's name from the registry. I think
the __del__() method will be called immediately when the
reference to the variable goes out of scope. Be careful:
the registry should NOT have references to the variable
objects themselves, or else their __del__() methods
will never be called.

QUESTION: In the future, when our input is in printable form,
how will we determine which variables are new, and how will we
translate variable names into variable objects?
ANSWER: To determine which variables are new,
our translator will simply keep a stack of dictionaries
of variable names. The translator won't actually
translate variable names into variable objects.
It will translate logic variable names into Python
variable names, and it will keep those in the stack
of dictionaries. Remember, the stack of dictionaries
is only used during translation, not while running
the proof.

NEW RULES and their new computational requirements:

UI:  1) matching a whole quantified formula:
	a) new branch in _match() for quantification
        b) addition of the variable of quantification
           to the interpretation dictionary that results from matching
        c) NOT needed: I think we never need a predicate in a match expression.
     2) changing variable: see BVE.
     3) reformulating (removing quantification): nothing new
EG:  nothing new. matching a whole formula, reformulating, and changing variable.
QNE: nothing new. matching a quantified subexpression, reformulating it.
QSE: checking that a subexpression contains no free occurrences of a specified
     individual variable. Beware of shadowing (as in DIFFICULT EXAMPLE).
BVE: changing variable in quantified subexpression: Beware of shadowing.
EI:  1) checking that a variable does not occur free in any previous
	undischarged assumption. How?????
     2) not new: instantiating a quantified formula. See UI.
     3) not new: calling a specified proof function. See CP.
     4) not new: checking that a formula contains no free occurrences of a
     	specified variable. See QSE.
UG:  nothing new. same as EI.

Suggested order of implementation:
1. QNE. matching a whole quantified formula as detailed above for UI
2. QSE. checking lack of free occurrences of a variable in a subexpression
3. BVE. changing variable

4. UI. 1-3 should furnish everything necessary
5. EG. 1-3 should furnish everything necessary

6. UG. checking lack of free occurrences of a variable in previous undischarged assumptions
7. EI. same, although this time using a specified proof function

PROBLEM: Qx[id:1] & (&x[id:2])(Px[id:2]) => Qx[id:1] & Px[id:2]
"""

class Var:
	count = 0;
	registry = {}
	def __init__(self, name = None):
		if name != None:
			if Var.registry.has_key(name):
				raise ValueError()
			self.data = name
		else:
			Var.count = Var.count + 1
			self.data = 'x' + str(Var.count)
		self.taint = 0
		Var.registry[self.data] = 1
	def __del__(self):
		Var.registry.__delitem__(self.data)
	def __str__(self):
		return self.data
	def __repr__(self):
		return 'Var(' + str(self) + ')'
	def get_name(self):
		return self.data
	def is_tainted(self):
		return self.taint
	def set_tainted(self, taint):
		self.taint = taint

class Quant:
	def __init__(self, quantifier, variable):
		if not _is_quantifier(quantifier):
			raise TypeError()
		if not isinstance(variable, Var):
			raise TypeError()
		self.quantifier = quantifier
		self.variable = variable
	def __cmp__(self, other):
		if not isinstance(other, Quant):
			return -1
		elif self.quantifier != other.quantifier:
			return cmp(self.quantifier, other.quantifier)
		else:
			return cmp(self.variable, other.variable)
	def __str__(self):
		return str(self.quantifier) + '(' + str(self.variable) + ')'
	def __repr__(self):
		return str(self)
	def get_quantifier(self):
		return self.quantifier
	def get_variable(self):
		return self.variable

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
	if type(l) == types.StringType and _is_statement_constant(l):
		return {l[0]: m}
	elif len(l) == 2 and _is_quantification(l[0]) and len(m) == 2 and _is_quantification(m[0]):
		if l[0].get_quantifier() != m[0].get_quantifier():
			raise LogicException()
		else:
			m1 = {l[0].get_variable(): m[0].get_variable()}
			m2 = _match(l[1], m[1])
			return dict(m1.items() + m2.items())
	elif (len(l) == 2 and _is_monadic_predicate(l[0]) and _is_individual(l[1])
		and len(m) == 2 and _is_monadic_predicate(m[0]) and _is_individual(m[1])):
		return {l[0]: m[0], l[1]: m[1]}
	elif len(l) == 2 and l[0] == neg and len(m) == 2 and m[0] == neg:
		return _match(l[1], m[1])
	elif len(l) == 3 and _is_binary(l[1]) and len(m) == 3 and m[1] == l[1]:
		return dict(_match(l[0],m[0]).items() + _match(l[2],m[2]).items())
	else:
		raise LogicException()


_strict_match = _match

def _bind(interp, formula):
	if _is_quantification(formula):
		if interp.has_key(formula.get_variable()):
			return Quant(formula.get_quantifier(), interp[formula.get_variable()])
		return formula
	elif (_is_statement_constant(formula) or _is_monadic_predicate(formula)
			or _is_individual(formula)):
		if interp.has_key(formula):
			return interp[formula]
		return formula
	elif formula == '~' or _is_binary(formula):
		return formula
	result = map(lambda x: _bind(interp, x), formula)
	return tuple(result)


def _replace_match(formula, rule_list):
	for rule in rule_list:
		if len(rule) == 3 and rule[2] == 1:
			try:
				interp = _strict_match(rule[0], formula)
				return _bind(interp, rule[1])
			except LogicException:
				pass
		else:
			try:
				interp = _match(rule[0], formula)
				return _bind(interp, rule[1])
			except LogicException:
				pass
	raise LogicException()


def _free_variables_in(formula):
	free_vars = {}
	ancestry = [[formula, {}]]
	
	while len(ancestry) > 0:
		parent = ancestry[-1][0]
		bound_vars = ancestry[-1][1]
		ancestry.pop()
		
		if type(parent) == types.TupleType:
			if len(parent) == 2:
				if _is_monadic_predicate(parent[0]):
					if not bound_vars.has_key(parent[1]):
						free_vars[parent[1]] = 1
				elif _is_quantification(parent[0]):
					var = parent[0].get_variable()
					bound_vars[var] = 1
					ancestry.append([parent[1], bound_vars])
				elif parent[0] == neg:
					ancestry.append([parent[1], bound_vars])
			elif len(parent) == 3:
				ancestry.append([parent[0], bound_vars])
				ancestry.append([parent[2], bound_vars])
	return free_vars
		

def _is_free_in(var, expr):
	f = _free_variables_in(expr)
	return f.has_key(var)
	
	
def _change_variable(formula, old_var, new_var):
	if (type(formula) == types.TupleType and len(formula) == 2
			and type(formula[0]) == types.StringType
			and _is_monadic_predicate(formula[0])):
		if formula[1] == old_var:
			result = (formula[0], new_var)
		else:
			result = formula
	elif (type(formula) == types.TupleType and (len(formula) != 2
			or type(formula[0]) != types.StringType
			or not isinstance(formula[0], Quant)
			or formula[0].get_variable() != old_var)):
		result = map(lambda x: _change_variable(x, old_var, new_var), formula)
		result = tuple(result)
	else:
		result = formula
	return result


def _replace_subexpression(formula, position_list, f):
	ancestry = []
	parent = formula
	parent_pos = None
	subexpression = formula
	for pos in position_list:
		parent = subexpression
		parent_pos = pos
		ancestry.append([parent, parent_pos])
		subexpression = parent[parent_pos]
	formula = f(subexpression)
	ancestry.reverse()
	for ancestor in ancestry:
		child = formula
		formula = []
		for i in range(0, len(ancestor[0])):
			if i == ancestor[1]:
				formula.append(child)
			else:
				formula.append(ancestor[0][i])
		formula = tuple(formula)
	return formula


def _vet_assumption(formula):

	# This is NOT thread-safe!
	free_vars = _free_variables_in(formula)
	tainted_vars = {}
	for var in free_vars:
		if not var.is_tainted():
			var.set_tainted(true)
		tainted_vars[var] = 1
	return tainted_vars


def _restore_conclusion(tainted_vars):

	# This is NOT thread-safe!
	for var in tainted_vars.keys():
		var.set_tainted(false)

	
class MPCProposition(Proposition):
	HINT_LEFT = 0
	HINT_RIGHT = 1

	def __init__(self, l):
		"Creates a new proposition of the specified form."
		if not _is_well_formed(l):
			raise TypeError()
		self.data = l
		
	def quantifier_negation_equivalence(self, position_list = []):
		"""
		~(&/v x)(~Px) <=> (v/& x)(Px)
		"""
		def QNE_body(formula):
			x = Var()
			return _replace_match(formula, [
				[ (neg, (Quant(forall, x), (neg, A))),  (Quant(exists, x), A) ],
				[ (neg, (Quant(exists, x), (neg, A))),  (Quant(forall, x), A) ],
				[ (Quant(forall, x), A),  (neg, (Quant(exists, x), (neg, A))) ],
				[ (Quant(exists, x), A),  (neg, (Quant(forall, x), (neg, A))) ],
			])
		return self.__class__(
			_replace_subexpression(self.data, position_list, QNE_body)
		)
	QNE = quantifier_negation_equivalence

	def quantifier_shift_equivalence(self, position_list = [], hint = None):
		"""
		D op (qu x)(Px) => (qu x)(D op Px)
		(qu x)(Px) op D => (qu x)(Px op D)
		(qu x)(D op Px) => D op (qu x)(Px)
		(qu x)(Px op D) => (qu x)(Px) op D
		
		where "qu" is a quantifier and "op" is a binary operator, but not "iff".
		If the operator is implication and the left operand is being shifted,
		then the quantifier changes.
		"""
		
		# It would make sense to enrich the pattern language of _match() in
		# order to abbreviate all of the following, as in the documentation string.
		
		def shift_left_in(formula):
			"D op (qu x)(Px) => (qu x)(D op Px)"
			bin_expr = formula
			quant = bin_expr[2][0]
			if _is_free_in(quant.get_variable(), bin_expr[0]):
				raise LogicException()
			return MPCProposition(
				(quant, (bin_expr[0], bin_expr[1], bin_expr[2][1]))
			)
		def shift_right_in(formula):
			"(qu x)(Px) op D => (qu x)(Px op D)"
			bin_expr = formula
			quant = bin_expr[0][0]
			var = quant.get_variable()
			if _is_free_in(var, bin_expr[2]):
				raise LogicException()
			if bin_expr[1] == impl:
				if quant.get_quantifier() == forall:
					quant = Quant(exists, var)
				else:
					quant = Quant(forall, var)
			return MPCProposition(
				(quant, (bin_expr[0][1], bin_expr[1], bin_expr[2]))
			)
		def shift_left_out(formula):
			"(qu x)(D op Px) => D op (qu x)(Px)"
			bin_expr = formula[1]
			quant = formula[0]
			if _is_free_in(quant.get_variable(), bin_expr[0]):
				raise LogicException()
			return MPCProposition(
				(bin_expr[0], bin_expr[1], (quant, bin_expr[2]))
			)
		def shift_right_out(formula):
			"(qu x)(Px op D) => (qu x)(Px) op D"
			bin_expr = formula[1]
			quant = formula[0]
			var = quant.get_variable()
			if _is_free_in(var, bin_expr[2]):
				raise LogicException()
			if bin_expr[1] == impl:
				if quant.get_quantifier() == forall:
					quant = Quant(exists, var)
				else:
					quant = Quant(forall, var)
			return MPCProposition(
				((quant, bin_expr[0]), bin_expr[1], bin_expr[2])
			)
		def shift_out(formula):
			# variable hint is a parameter of the enclosing function
			if not _is_quantification(formula[0]):
				raise LogicException()
			bin_expr = formula[1]
			if (type(bin_expr) != types.TupleType
					or len(bin_expr) != 3
					or bin_expr[1] == iff):
				raise LogicException()
			
			# Which side?
			if hint == MPCProposition.HINT_LEFT:
				return shift_left_out(formula)
			elif hint == MPCProposition.HINT_RIGHT:
				return shift_right_out(formula)
			else:
				# Just try them and see if only one works.
				try:
					answer = shift_left_out(formula)
					
					is_ambiguous = 1
					try:
						shift_right_out(formula)
					except LogicException:
						is_ambiguous = 0
					if is_ambiguous:
						raise LogicException('QSE needs a hint!')
						
					return answer
				except LogicException:
					return shift_right_out(formula)
		def shift_in(formula):
			# variable hint is a parameter of the enclosing function
			bin_expr = formula
			if bin_expr[1] == iff:
				raise LogicException()
			
			# Which side?
			if hint == MPCProposition.HINT_LEFT:
				if (type(bin_expr[2]) != types.TupleType
						or not _is_quantification(bin_expr[2][0])):
					raise LogicException()
				
				return shift_left_in(formula)
			elif hint == MPCProposition.HINT_RIGHT:
				if (type(bin_expr[0]) != types.TupleType
						or not _is_quantification(bin_expr[0][0])):
					raise LogicException()
				
				return shift_right_in(formula)
			elif (type(bin_expr[2]) == types.TupleType
					and _is_quantification(bin_expr[2][0])):
				quant = bin_expr[2][0]
				if (type(bin_expr[0]) == types.TupleType
					and _is_quantification(bin_expr[0][0])):
					
					# Just try them and see if only one works.
					try:
						answer = shift_left_in(formula)
						
						is_ambiguous = 1
						try:
							shift_right_in(formula)
						except LogicException:
							is_ambiguous = 0
						if is_ambiguous:
							raise LogicException('QSE needs a hint!')
							
						return answer
					except LogicException:
						return shift_right_in(formula)
				else:
					return shift_left_in(formula)
			elif (type(bin_expr[0]) == types.TupleType
					and _is_quantification(bin_expr[0][0])):
				return shift_right_in(formula)
			else:
				raise LogicException()
		def QSE_body(formula):
			if type(formula) != types.TupleType:
				raise LogicException()
			if len(formula) == 2:
				return shift_out(formula)
			elif len(formula) == 3:
				return shift_in(formula)
			else:
				raise LogicException()
		return self.__class__(
			_replace_subexpression(self.data, position_list, QSE_body)
		)
	QSE = quantifier_shift_equivalence
	
	def bound_variable_equivalence(self, position_list, new_var):
		def BVE_body(formula):
			if (type(formula) != types.TupleType
					or len(formula) != 2
					or not _is_quantification(formula[0])):
				raise LogicException()
			if _is_free_in(new_var, formula):
				raise LogicException("Can't change to already free variable!")
			return (
				Quant(formula[0].get_quantifier(), new_var),
				_change_variable(
					formula[1],
					formula[0].get_variable(),
					new_var
				)
			)
		return self.__class__(
			_replace_subexpression(self.data, position_list, BVE_body)
		)
	BVE = bound_variable_equivalence
	
	def universal_instantiation(self, var=None):
		if (type(self.data) != types.TupleType
				or len(self.data) != 2
				or not _is_quantification(self.data[0])
				or self.data[0].get_quantifier() != forall):
			raise LogicException()
		if var == None:
			return self.__class__(self.data[1])
		elif _is_free_in(var, self.data[1]):
			raise LogicException("Can't instantiate to already free variable!")
		else:
			return self.__class__(
				_change_variable(self.data[1], self.data[0].get_variable(), var)
			)
	UI = universal_instantiation
	
	def existential_generalization(self, var=None, new_var=None):
		if var == None:
			free_vars = _free_variables_in(self.data).keys()
			if len(free_vars) != 1:
				raise LogicException()
			else:
				var = free_vars[0]
		elif not _is_free_in(var, self.data):
			raise LogicException()
		
		if new_var != None:
			if _is_free_in(new_var, self.data):
				raise LogicException()
			return self.__class__((
				Quant(exists, new_var),
				_change_variable(self.data, var, new_var)
			))
		else:
			return self.__class__((
				Quant(exists, var),
				self.data
			))
	EG = existential_generalization
	
	def universal_generalization(self, var=None, new_var=None):
		if var == None:
			free_vars = _free_variables_in(self.data).keys()
			if len(free_vars) != 1:
				raise LogicException()
			else:
				var = free_vars[0]
		elif not _is_free_in(var, self.data):
			raise LogicException()
		
		if var.is_tainted():
			raise LogicException()
		
		if new_var != None:
			if _is_free_in(new_var, self.data):
				raise LogicException()
			return self.__class__((
				Quant(forall, new_var),
				_change_variable(self.data, var, new_var)
			))
		else:
			return self.__class__((
				Quant(forall, var),
				self.data
			))
	UG = universal_generalization

	def existential_instantiation(self, proof_function, var=None):
		if (type(self.data) != types.TupleType or len(self.data) != 2
				or not _is_quantification(self.data[0])
				or self.data[0].get_quantifier() != exists):
			raise LogicException()
		if type(proof_function) != types.FunctionType:
			raise TypeError()
			
		if var == None:
			var = self.data[0].get_variable()
			assumption = self.__class__(self.data[1])
		elif _is_free_in(var, self.data[1]):
			raise LogicException("Can't instantiate to already free variable!")
		else:
			assumption = self.__class__(
				_change_variable(self.data[1], var)
			)
			if not _is_free_in(var, assumption.data):
				raise LogicException()
		
		if var.is_tainted():
			raise LogicException()
		new_vars = _vet_assumption(assumption)
		conclusion = proof_function(assumption)
		if _is_free_in(var, conclusion):
			raise LogicException()
		_restore_conclusion(new_vars)
		return self.__class__(conclusion)
	EI = existential_instantiation



_proposition_class = MPCProposition

def checked_proposition(object):
	if not isinstance(object, _proposition_class):
		raise TypeError()
	return object

def conditional_proof(proof_function):
	"""
	conditional_proof(anything_proves_itself)(MPCProposition(A))
		== MPCProposition((A, impl, A))
	def anything_proves_itself(p):
		return p
	
	1. |	A	by assumption
	2. A -> A	by 1 - conditional proof
	"""
	
	def CP_body(assumption):
		new_vars = _vet_assumption(assumption)
		antecedent = checked_proposition(assumption)[:]
		consequent = proof_function(assumption)
		consequent = checked_proposition(consequent)[:]
		conclusion = _proposition_class((
			antecedent,
			impl,
			consequent
		))
		_restore_conclusion(new_vars)
		return conclusion
	if type(proof_function) != types.FunctionType:
		raise TypeError()
	return CP_body
CP = conditional_proof

def indirect_proof(proof_function):
	"""
	IP(anything_proves_assumption_A_conjoined_with_it)(MPCProposition((neg, A)))
		== MPCProposition((neg, (neg, A)))
	assumption = MPCProposition(A)
	def anything_proves_assumption_A_conjoined_with_it(p):
		return Conj(assumption, p)
	
	1. |	A		by assumption
	2. |	|	~A	by assumption
	3. |	|	A & ~A	by 1, 2 - conjunction
	4. |	~~A		by 2 - indirect proof
	"""
	def indirect_proof_result(proof_function, assumption):
		checked_proposition(assumption)
		new_vars = _vet_assumption(assumption)
		interp = _strict_match((A, conj, (neg, A)), proof_function(assumption))
		conclusion = _proposition_class((neg, assumption[:]))
		_restore_conclusion(new_vars)
		return conclusion
	if type(proof_function) != types.FunctionType:
		raise TypeError()
	return lambda assumption: indirect_proof_result(proof_function, assumption)
IP = indirect_proof
