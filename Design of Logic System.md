Designing a system for computational verification of propositional logic
========================================================================

Aaron Mansheim, 2002


Introduction
------------

In its relatively brief history, computer science has provided a whole new approach to the age-old foundations of mathematics. Mathematics, on the other hand, is what makes computer science scientific. The two fields are closely related in many ways. One key relationship between the two fields is in proof theory. Modern mathematics is based on proofs. Proofs tell us how to use standard rules of inference to turn something that we know into something that we want to know. The process of inference is computational. If we describe the steps of a proof formally enough, we can make a computer program that follows each step to produce the logical result.

A system for describing proofs this formally can be useful. It requires us to write proofs without relying on anyone else to supply necessary details. It makes manifest that anyone who follows the necessary steps, even a computer, will reach the logical result.


Goals
-----

1. To create a computer system in which we can implement logical constructions as programs. That is, each program will represent a proof in propositional logic. Running the program will cause the system to perform a verification of the proof.

2. To use a simple, formal programming language (a subset of Lisp) to implement this system.

    Note: We're discussing two programming environments. The first one is the Lisp-like language that we use to build a logic system. The second is the logic system itself, which can be used to process proofs. These two environments are related, but at times we need to consider each without worrying about details of the other.

3. To make the system itself very small.


Design Considerations
---------------------

There are many symbols in logical propositions. There are many rules of inference in propositional logic. We would like to start with a minimal set and derive the rest using proofs. We will need at least one way to combine truth values and at least one rule of inference. In fact, we can get away with using only one of each.

To combine truth values, we will need a binary operation, that is, one that requires two input values to produce an output value. When we need to combine more than two values, we can combine them in pairs, then combine pairs of those results, and so on.


An Operation
------------

Digital circuit designers know that the binary logical operation called NAND can be used to build any digital logic operation. When we combine two truth values with NAND, the result is false only when both input values are true. Otherwise, the result is true.

In our logic system, we could define NAND in exactly that way. But it will be unusual in logical proofs to define the truth of a certain proposition by the values of its variables. It will be much more usual simply to state that certain propositions are true or false no matter what values their variables may have. If we define NAND in this more usual way, we may be able to avoid building mechanisms in our system that would only be used in this definition.

There can only be sixteen binary logical operations. Each one of the possible operations is characterized by the four values that it gives for the four possible pairs of input values: true-true, true-false, false-true, and false-false. As we said, NAND is the one that produces the output values false, true, true, and true respectively. But we would rather not define NAND that way. It would be nice to define NAND by stating some propositions that are only true when the NAND operation is given the one correct interpretation out of the sixteen possibilities. Just a few propositions in one variable, with no constants, should do the trick. That will keep us from having to define constants TRUE and FALSE, which are also rarely used in proofs.

In fact, that way will not work, although we will later find a modified approach. We cannot define the NAND operation by listing true propositions in an attempt to imply the correct interpretation of NAND. The reason is that there is a binary operation whose result is always true regardless of the inputs. Any proposition in one variable and one binary operation, with no constants, is true when the operator is interpreted as the always-true operation.

Fortunately, we will see that the always-true operation is the only problem with this approach, so we can specifically rule it out. We can simply say that "A NAND A" is not always true. We will use two kinds of propositions: those that are always true, and those that are not always true. We will say that the propositions listed as always true are "positive" and those listed as not always true are "negative." We will consider the two kinds of propositions in detail when we want to think more about quantifiers in logic, but for now we simply mention that they will be useful.

What positive propositions will we use to define NAND? The simplest positive proposition using NAND is "A NAND (A NAND A)". Apart from the always-true operation, only one other operation can replace NAND to make a positive proposition of "A NAND (A NAND A)". That operation is the one that takes the four possible pairs of input values and produces the output values true, false, true, and true respectively. We can call it "IF" because it is how logicians interpret the word "if." We notice that IF is not symmetrical in its two inputs: although "A IF (A IF A)" is always true, "(A IF A) IF A" is not always true. In contrast, "(A NAND A) NAND A" is always true. We have our three propositions for NAND:

* "A NAND (A NAND A)" is always true.
* "(A NAND A) NAND A" is always true.
* "A NAND A" is not always true.


A Rule of Inference
-------------------

Now we need a rule of inference. Logicians know that the classical rule of inference called "modus tollens" can be used to derive any other rule of inference in propositional logic. It takes two true statements with a certain relationship and infers that a third related statement is true. The relationship is as follows. From a statement "P" and a statement "NOT Q IMPLIES NOT P" we infer the statement "Q".

We have agreed to start only with the operation NAND. For our initial version of modus tollens, we will write the statement "NOT Q IMPLIES NOT P" equivalently as "(Q NAND Q) NAND P".

Later, we will consider rules of inference that make use of negative propositions.


Proofs
------

A proof in our system will consist of a name, assertions, inferences, and conclusions. The name of the proof simply states a name that can be used later. An assertion adds a proposition, called a "premise" of the proof, to the list. An inference refers to two propositions already listed, applies a rule of inference to them (initially only modus tollens), and adds the result to the list. A result of modus tollens is not a premise. A conclusion identifies one of the listed propositions as a "conclusion" of the proof.

The result of a proof is a new rule of inference. From the premises of the proof it infers the conclusions of the proof. The name of the proof becomes the name of the new rule of inference.

Later, we will consider how to state rules of inferences as propositions, and the usefulness of such a move.

A "proof" of our modus tollens that uses our built-in modus tollens might appear as follows.

    proof modus_tollens_by_modus_tollens
    assert p (P)
    assert not_q_implies_not_p_in_nand ((Q NAND Q) NAND P)
    // The two preceding statements are assertions that are local to this proof.
    derive q modus_tollens p not_q_implies_not_p_in_nand
    conclude q

In a more procedural style, the same proof might appear as follows.

    modus_tollens_by_modus_tollens:
    p = premise("P")
    not_q_implies_not_p_in_nand = premise("(Q NAND Q) NAND P")
    // The two preceding statements are assertions that are local to this proof.
    // Each implies an argument to the proof whose form must match the displayed expression.
    // Variables in the displayed expression bind to subexpressions in the argument.
    q = modus_tollens(p, not_q_implies_not_p_in_nand)
    return q


Definitions
-----------

We will soon want to allow the naming of new operations. Once we have named an operation, we can define it by positive propositions that allows us to equate the new operation with an expression in known operations. For example, the following two positive propositions define "P IMPLIES Q" as "P NAND (Q NAND Q)":

* ((P IMPLIES Q) NAND (P IMPLIES Q)) NAND (P NAND (Q NAND Q))
* ((P NAND (Q NAND Q)) NAND (P NAND (Q NAND Q))) NAND (P IMPLIES Q)

We will also want to name symbols that represent expressions. We can simply use positive propositions that equate a new symbol with the desired expression. For example, the following two positive propositions define "A" as "P IMPLIES Q":

* ((P IMPLIES Q) NAND (P IMPLIES Q)) NAND A
* (A NAND A) NAND (P IMPLIES Q)


Testbed 
-------

Our first set of test cases for the system, then, will be a set of proofs that define the usual operations and inference rules of propositional logic. For example, we will define the operation IMPLIES:

assert implies-from-nand
* ((P IMPLIES Q) NAND (P IMPLIES Q)) NAND (P NAND (Q NAND Q))

        proof def-implies-from-nand
        assert p-implies-q-in-nand (P NAND (Q NAND Q))
        comment The above assertion is local to this proof.
        derive p-implies-q modus-tollens p-implies-q-in-nand  implies-from-nand

assert implies-to-nand
* ((P NAND (Q NAND Q)) NAND (P NAND (Q NAND Q))) NAND (P IMPLIES Q)

        proof def-implies-to-nand
        assert p-implies-q (P IMPLIES Q)
        derive p-implies-q-in-nand modus-tollens p-implies-q implies-to-nand

We will want to prove the inference rule known as "modus ponens". From "P" and "P IMPLIES Q" we infer "Q".

    proof modus-ponens
    assert p P
    assert p-implies-q (P IMPLIES Q)
    derive p-implies-q-in-nand def-implies-to-nand p-implies-q
    check p-implies-q-in-nand (P NAND (Q NAND Q))
    ...

    assert nand-axiom-right (A NAND (A NAND A))
    assert nand-axiom-left ((A NAND A) NAND A)
    assert-negatively nand-axiom-falsifiability (A NAND A)

    proof nand-commutes
    assert a-nand-b (A NAND B)

    ...
    check b-nand-a (B NAND A)

    comment Modus tollens in nand gets Q from P and (Q NAND Q) NAND 
