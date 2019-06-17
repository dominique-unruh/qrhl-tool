(*

CHSH proof for EasyCrypt
By Dominique Unruh

EasyCrypt proof that an adversary has probability at most 3/4 to win
in the CHSH game.  This shows that EasyCrypt is not sound for quantum
adversaries because it is well-known that quantum adversaries can win
CHSH with a probability >3/4.

The CHSH game is modeled in the module CHSH below, and the main result
is the lemma chsh at the end of this file.

Tested with EasyCrypt commit 44ae0e6b7eedfa87b74b8d9d12208afeddabee3d
and SMT provers Alt-Ergo 1.30, Z3 4.5.0, Eprover 1.9.1-001.

*)

require import Bool.
require import Real.
require import Distr.
require import List.
require FSet.
require import DBool.

(* An adversary consists of three parts. A setup routine that produces
a joint initial state, and two players A and B that play the actual
CHSH game.

they may share variables with the setup routine.

The setup routine is modeled as a module of type Setup, and A an B are
modules of type Player.
 *)

module type Setup = {
  (* This routine initializes the states of A and B with possibly
     correlated information *)
  proc setup() : unit
}.

module type Player = {
  (* This invokes the player A or B with input t, and returns the
     player's response *)
  proc invoke(t:bool) : bool
}.

(* This module contains the description of the CHSH game.

    CHSH(S,A,B).run() returns a Boolean that indicates whether the
    S.setup();
    x = ${0,1};
    y = ${0,1};
    a = A.invoke(x);
    b = B.invoke(y);
  return (a^^b) = (x/\y);
  }
}.

(* A section is a local context with local module declarations (S,A,B)
and assumptions (lossless_S,lossless_A,lossless_B). At the end of the
section, those assumptions will be transformed into premises for the
lemmas proven in the section. (I.e., even though we use the command
"axiom", not axioms are introduced globally.) *)

section.

(* We consider an fixed adversary that consists of a setup S, and
players A and B. B is assumed not to share global variables with A
(expressed by the {A}-part of the declaration of B). *)
declare module S:Setup.
declare module A:Player.
declare module B:Player{A}.

(* We only consider adversaries that terminate with probability 1 *)
axiom lossless_S: islossless S.setup.
axiom lossless_A: islossless A.invoke.
axiom lossless_B: islossless B.invoke.

(* An auxiliary function to abbreviate the winning condition of CHSH *)
op win (x y a b:bool) = (a^^b) = (x/\y).

(* C is a module with auxiliary functions that split the CHSH game
into several procedures. C.run() does the same as CHSH(S,A,B).run(),
but splitting it into several routines makes it easier to refer to
parts of the game in the lemmas below. *)

local module C = {
  var a,b,x,y : bool
  proc ab() : unit = {
    a = A.invoke(x);
    b = B.invoke(y);
  }
  proc xyab(): unit = {
    x = ${0,1};
    y = ${0,1};
    ab(); 
  }
  proc run() : bool = {
      S.setup();
      xyab();
      return win x y a b;
  }
}.

(* Auxiliary lemma *)
lemma le_refl (r:real): r <= r. smt. qed.

(* An auxiliary constant for protecting subterms from rewriting *)
op protect (x:bool) = x.
lemma protect x: protect x => x. trivial. qed.

(* Auxiliary lemma *)
lemma not_false r: r <> false => r=true.
    case r; by trivial.
qed.

(* Auxiliary lemma *)
lemma oneminus r: 1%r - (1%r - r) = r.
    smt.
qed.

(* Auxiliary lemma *)
lemma minus_leq (r s t:real): s >= r-t => r-s <= t.
    smt.
qed.

(* This lemma models the fact that the probability that A returns true
on a given input x depends only on x and the initial state of A (but
not on any other global variables).

This is done by saying: 
If the global variables of A in memory &m (written (glob A){m}) have the value globs.`1,
and if pa is the probability that A.invoke(x)=true on initial memory &m,
then A.invoke with precondition "global variables of A have value globs.`1 and the argument of A.invoke is x" reaches postconditon "result is a" with probability pa or 1-pa (depending on whether a=true or a=false).
*)

local lemma a_prob x a pa (globs:glob A*glob B) &m:
    (glob A){m} = globs.`1 =>
    pa = Pr[A.invoke(x) @ &m : res = true] =>
    phoare [ A.invoke : (glob A) = globs.`1
             /\ t=x ==> res=a ] = (if a then pa else 1%r-pa).
proof.
move => HglobA Hpa.
case a => Ha.
(* Case a=1 *)
rewrite Hpa.
bypr => &m0 [globA Hx].
rewrite  Hx.
byequiv => //.
  conseq (_: ={t} /\ ={glob A} ==> ={res});
    [ by rewrite globA HglobA; trivial | proc *; by call (_:true); auto ].
(* Case a=0 *)
rewrite Hpa.
bypr => &m0 [globA Hx].
rewrite  Hx.
cut H: Pr[A.invoke(x) @ &m : res = true] = Pr[A.invoke(x) @ &m : !(res = false)].
  by byequiv => //; proc *; call (_:true); auto; progress; apply not_false; trivial. 
rewrite H.
rewrite Pr [mu_not].
cut Hterm: Pr[A.invoke(x) @ &m : true] = 1%r.
    by byphoare => //; apply lossless_A.
rewrite Hterm.
rewrite oneminus.
byequiv => //.
  conseq (_: ={t} /\ ={glob A} ==> ={res});
    [ by rewrite globA HglobA; trivial | proc *; by call (_:true); auto ].
qed.
  
(* Analogous to a_prob above, but for B *)
local lemma b_prob y b pb (globs:glob A*glob B) &m:
    (glob B){m} = globs.`2 =>
    pb = Pr[B.invoke(y) @ &m : res = true] =>
    phoare [ B.invoke : (glob B) = globs.`2 /\ t = y ==> res=b ] = (if b then pb else 1%r-pb).
proof.
move => HglobB Hpb.
case b => Hb.
(* Case b=1 *)
rewrite Hpb.
bypr => &m0 [globB Hx].
rewrite  Hx.
byequiv => //.
  conseq (_: ={t} /\ ={glob B} ==> ={res});
    [ by rewrite globB HglobB; trivial | proc *; by call (_:true); auto ].
(* Case b=0 *)
rewrite Hpb.
bypr => &m0 [globB Hx].
rewrite  Hx.
cut H: Pr[B.invoke(y) @ &m : res = true] = Pr[B.invoke(y) @ &m : !(res = false)].
  by byequiv => //; proc *; call (_:true); auto; progress; apply not_false; trivial. 
rewrite H.
rewrite Pr [mu_not].
cut Hterm: Pr[B.invoke(y) @ &m : true] = 1%r.
    by byphoare => //; apply lossless_B.
rewrite Hterm.
rewrite oneminus.
byequiv => //.
  conseq (_: ={t} /\ ={glob B} ==> ={res});
    [ by rewrite globB HglobB; trivial | proc *; by call (_:true); auto ].
qed.

(* Auxiliary lemma *)
lemma neq_or_imp (x a r:bool): x <> a => !((x = a) /\ r).
    smt.
qed.

(* This lemma says that, for given initial states of A and B, 
   and given inputs x and y, the (joint) probability of outputs a and b is the 
   product of the probabilities of output a and of output b
   (i.e., for fixed initial states and inputs, the outputs are independent.)

   This lemma is false in the quantum case.

   Reason: If glob A and glob B are entangled, the behaviour of C.ab
   cannot be predicted by the marginal states of A and B alone, i.e.,
   C.a and C.b are not independently distributed and therefore we
   phoare does not equal a product of probabilities.
*)
local lemma ab_prob x y a b pa pb (globs:glob A*glob B) &m:
    (glob A){m} = globs.`1 =>
    (glob B){m} = globs.`2 =>
    pa = Pr[A.invoke(x) @ &m : res = true] =>
    pb = Pr[B.invoke(y) @ &m : res = true] =>
    phoare [ C.ab : (glob A) = globs.`1 /\ (glob B) = globs.`2 /\ C.x = x /\ C.y = y ==> C.a = a /\ C.b = b /\ C.x = x /\ C.y = y ] = 
    ((if a then pa else 1%r-pa)*(if b then pb else 1%r-pb)).
proof.
move => HglobA HglobB Hpa Hpb.
   That is not true for quantum variables entangled with A.

   (We assume here that "glob A"/"glob B" refers to all variables of
   A/B. If it refers only to the classical variables, the lemma is
call (_: (glob B) = globs.`2 /\ t=y ==> res=b);
  [ by apply (b_prob y b pb globs &m) => // | by auto ].
seq 1: (true) 1%r 0%r _ 0%r (C.a<>a) => //.
  by call (_:true); auto; trivial.
  by hoare; auto => &hr H; apply (neq_or_imp (C.a{hr}) a (C.b{hr} = b /\ C.x{hr} = x /\ C.y{hr} = y)) => //.
qed.

(* An auxiliary function to abbreviate the losing condition of CHSH *)
   (in term of the product of A's and B's individual output probabilities pa,pb)
   for the probability that A and B output given values a and b and lose
   (for fixed initial states and inputs).
*)
local lemma ab_prob2 x y a b pa pb (globs:glob A*glob B) &m:
    (glob A){m} = globs.`1 =>
    (glob B){m} = globs.`2 =>
    pa = Pr[A.invoke(x) @ &m : res = true] =>
    pb = Pr[B.invoke(y) @ &m : res = true] =>
    phoare [ C.ab : (glob A) = globs.`1 /\ (glob B) = globs.`2 /\ C.x = x /\ C.y = y ==> 
      C.a = a /\ C.b = b /\ lose C.x C.y C.a C.b ] = 
    (if (win x y a b) then 0%r else ((if a then pa else 1%r-pa)*(if b then pb else 1%r-pb))).
qed.

(* A formula for the probability that A and B lose in terms of their inputs and
   the probabilities pa,pb that A,B output 1.
*)
op failprob1 (pa pb:real) (x y:bool) : real = 
   let out0 = pa*pb + (1%r-pa)*(1%r-pb) in
      if x/\y then out0 else 1%r-out0.


(* This lemma shows that the probability that A and B lose (for fixed inputs and initial states)
   is indeed failprob1.
  

*)
local lemma ab_prob3 x y pa pb (globs:glob A*glob B) &m:
    (glob A){m} = globs.`1 =>
    (glob B){m} = globs.`2 =>
    pa = Pr[A.invoke(x) @ &m : res = true] =>
    pb = Pr[B.invoke(y) @ &m : res = true] =>
    phoare [ C.ab : (glob A) = globs.`1 /\ (glob B) = globs.`2 /\ C.x = x /\ C.y = y ==> 
      lose C.x C.y C.a C.b ] = 
      (failprob1 pa pb x y).
proof.
move => globA globB Hpa Hpb.
pose lose_atrue :=
  (if (win x y true true) then 0%r else (pa*pb)) + 
   if (win x y true false) then 0%r else (pa*(1%r-pb)).
pose lose_afalse :=
  (if (win x y false true) then 0%r else ((1%r-pa)*pb)) + 
   if (win x y false false) then 0%r else ((1%r-pa)*(1%r-pb)).
conseq (_: _ ==> 
  ((C.a = true /\ C.b = true /\ lose C.x C.y C.a C.b)
    \/ (C.a = true /\ C.b = false /\ lose C.x C.y C.a C.b))
\/((C.a = false /\ C.b = true /\ lose C.x C.y C.a C.b)
    \/ (C.a = false /\ C.b = false /\ lose C.x C.y C.a C.b)));
        first by smt.
  phoare split lose_atrue lose_afalse 0%r.
    by rewrite /lose_atrue /lose_afalse /failprob1 /win 
               xor_true xor_false; progress; case (C.y{hr}); case (C.x{hr}); smt.  
  phoare split (if (win x y true true) then 0%r else (pa*pb))
               (if (win x y true false) then 0%r else (pa*(1%r-pb)))
               0%r => //.
    by apply (ab_prob2 x y true true pa pb globs &m) => //.
    by apply (ab_prob2 x y true false pa pb globs &m) => //.
  hoare; conseq (_: true==>true) => //; smt.
  phoare split (if (win x y false true) then 0%r else ((1%r-pa)*pb))
               (if (win x y false false) then 0%r else ((1%r-pa)*(1%r-pb)))
               0%r => //.
    by apply (ab_prob2 x y false true pa pb globs &m) => //.
    by apply (ab_prob2 x y false false pa pb globs &m) => //.
  hoare; conseq (_: true==>true) => //; smt.
  hoare; conseq (_: true==>true) => //; smt.
qed.

(* Auxiliary abbreviations *)
op quarter = 1%r/4%r.
op half = 1%r/2%r.

(* A polynomial expression for the probability that A and B fail,
   in terms of the probabilities that A outputs 1 on input 0 (pa0), on input 1 (pa1),
   that B outputs 1 on input 0 (pb0), on input 1 (pb1).
*)
op failpoly pa0 pa1 pb0 pb1 =
  quarter*(failprob1 pa1 pb1 true true)

  pa0,pa1,pb0,pb1 are as in failpoly above.
*)
op failpoly_xy x y pa0 pa1 pb0 pb1 =
   failprob1 (if x then pa1 else pa0) (if y then pb1 else pb0) x y.

(* Shows that the probability that A and B lose and the input are x,y is indeed failprob1/4.

   (That is, while earlier we were considering fixed inputs x,y, now we consider the game where 
   C.xyab that includes the choosing of x,y, and the invocation of A,B, but not the 
   initial invocation of S.)
*)
local lemma xyab_prob x y pa0 pa1 pb0 pb1 (globs:glob A*glob B) &m:
    (glob A){m} = globs.`1 =>
    (glob B){m} = globs.`2 =>
    pa0 = Pr[A.invoke(false) @ &m : res = true] =>
    pa1 = Pr[A.invoke(true) @ &m : res = true] =>
    pb0 = Pr[B.invoke(false) @ &m : res = true] =>
    pb1 = Pr[B.invoke(true) @ &m : res = true] =>
    phoare [ C.xyab : (glob A) = globs.`1 /\ (glob B) = globs.`2 ==> 
      C.x=x /\ C.y=y /\ lose C.x C.y C.a C.b ] = 
      (quarter*failpoly_xy x y pa0 pa1 pb0 pb1).
proof.
  by auto.
  by rnd; rewrite /half; auto; smt. 
seq 1: (C.y = y) half (failpoly_xy x y pa0 pa1 pb0 pb1)
                 half 0%r ((glob A)=globs.`1 /\ (glob B)=globs.`2 /\ C.x=x).
  by auto.
  by rnd; rewrite /half; auto; smt. 
  conseq (_: _ ==> _: = (failprob1 pa pb x y)) => //.
  call (_: (glob A) = globs.`1 /\ (glob B) = globs.`2 /\ C.x = x /\ C.y = y ==> lose C.x C.y C.a C.b) => //.
  apply (ab_prob3 x y pa pb globs &m) => //; 
    rewrite /pa /pb; [ case x; trivial | case y; trivial ].
    by hoare; conseq (_: C.y<>y==>true) => //; smt.
  by trivial.
  by hoare; conseq (_: C.x<>x==>true) => //; smt.
  by auto.  
qed.


(* Shows that the probability that A and B lose is indeed failpoly *)
local lemma xyab_prob2 pa0 pa1 pb0 pb1 (globs:glob A*glob B) &m:
    (glob A){m} = globs.`1 =>
    (glob B){m} = globs.`2 =>
    pa0 = Pr[A.invoke(false) @ &m : res = true] =>
    pa1 = Pr[A.invoke(true) @ &m : res = true] =>
    pb0 = Pr[B.invoke(false) @ &m : res = true] =>
    pb1 = Pr[B.invoke(true) @ &m : res = true] =>
    phoare [ C.xyab : (glob A) = globs.`1 /\ (glob B) = globs.`2 ==> 
      lose C.x C.y C.a C.b ] = 
      (failpoly pa0 pa1 pb0 pb1).
proof.
  move => globA globB Hpa0 Hpa1 Hpb0 Hpb1.
  conseq (_: _ ==> 
     ((C.x=true /\ C.y=true /\ lose C.x C.y C.a C.b)
  \/ (C.x=true /\ C.y=false /\ lose C.x C.y C.a C.b))
  \/ ((C.x=false /\ C.y=true /\ lose C.x C.y C.a C.b)
  \/ (C.x=false /\ C.y=false /\ lose C.x C.y C.a C.b)));
      first by smt.
  phoare split
   (quarter*failprob1 pa1 pb1 true true + quarter*failprob1 pa1 pb0 true false)
   (quarter*failprob1 pa0 pb1 false true + quarter*failprob1 pa0 pb0 false false)
     0%r; first smt.
  phoare split
   (quarter*failprob1 pa1 pb1 true true)
   (quarter*failprob1 pa1 pb0 true false)
     0%r; first smt.
  by apply (xyab_prob true true pa0 pa1 pb0 pb1 globs &m) => //.
  by apply (xyab_prob true false pa0 pa1 pb0 pb1 globs &m) => //.
  by hoare; conseq (_: true==>true) => //; smt.
  phoare split
   (quarter*failprob1 pa0 pb1 false true)
   (quarter*failprob1 pa0 pb0 false false)
     0%r; first smt.
  by apply (xyab_prob false true pa0 pa1 pb0 pb1 globs &m) => //.
  by apply (xyab_prob false false pa0 pa1 pb0 pb1 globs &m) => //.
  by hoare; conseq (_: true==>true) => //; smt.
  by hoare; conseq (_: true==>true) => //; smt.
qed. 

(* Auxiliary lemma *)
lemma mult_comm (a b:real): a*b = b*a. smt. qed.

(* Auxiliary lemma *)
lemma real_ge_trans: forall (b a c:real), 
 a >= b => b >= c => a >= c
by [].


(* Shows that failpoly>=1/4 (assuming that pa0,pa1,pb0,pb1 are probabilities). *)
lemma failpoly_bound pa0 pa1 pb0 pb1:
    pa0<=1%r => pa0>=0%r => pa1<=1%r => pa1>=0%r =>
    pb0<=1%r => pb0>=0%r => pb1<=1%r => pb1>=0%r =>
    quarter <= failpoly pa0 pa1 pb0 pb1.
    move => pa0leq pa0geq pa1leq pa1geq pb0leq pb0geq pb1leq pb1geq. 

      pa0*pa1*pb0*pb1*                  failpoly 1%r 1%r 1%r 1%r
    + pa0*pa1*pb0*(1%r-pb1)*            failpoly 1%r 1%r 1%r 0%r
    + pa0*pa1*(1%r-pb0)*pb1*            failpoly 1%r 1%r 0%r 1%r
    + pa0*pa1*(1%r-pb0)*(1%r-pb1)*      failpoly 1%r 1%r 0%r 0%r
    + pa0*(1%r-pa1)*pb0*pb1*            failpoly 1%r 0%r 1%r 1%r
    + pa0*(1%r-pa1)*pb0*(1%r-pb1)*      failpoly 1%r 0%r 1%r 0%r
    + pa0*(1%r-pa1)*(1%r-pb0)*pb1*      failpoly 1%r 0%r 0%r 1%r
    + pa0*(1%r-pa1)*(1%r-pb0)*(1%r-pb1)*failpoly 1%r 0%r 0%r 0%r

    + (1%r-pa0)*pa1*pb0*pb1*                  failpoly 0%r 1%r 1%r 1%r
    + (1%r-pa0)*pa1*pb0*(1%r-pb1)*            failpoly 0%r 1%r 1%r 0%r
    + (1%r-pa0)*pa1*(1%r-pb0)*pb1*            failpoly 0%r 1%r 0%r 1%r
    + (1%r-pa0)*pa1*(1%r-pb0)*(1%r-pb1)*      failpoly 0%r 1%r 0%r 0%r
    + (1%r-pa0)*(1%r-pa1)*pb0*pb1*            failpoly 0%r 0%r 1%r 1%r
    + (1%r-pa0)*(1%r-pa1)*pb0*(1%r-pb1)*      failpoly 0%r 0%r 1%r 0%r
    + (1%r-pa0)*(1%r-pa1)*(1%r-pb0)*pb1*      failpoly 0%r 0%r 0%r 1%r
    + (1%r-pa0)*(1%r-pa1)*(1%r-pb0)*(1%r-pb1)*failpoly 0%r 0%r 0%r 0%r.

    pose failpoly_quarter := 
      pa0*pa1*pb0*pb1*                  quarter
    + pa0*pa1*pb0*(1%r-pb1)*            quarter
    + pa0*pa1*(1%r-pb0)*pb1*            quarter
    + pa0*pa1*(1%r-pb0)*(1%r-pb1)*      quarter
    + pa0*(1%r-pa1)*pb0*pb1*            quarter
    + pa0*(1%r-pa1)*pb0*(1%r-pb1)*      quarter
    + pa0*(1%r-pa1)*(1%r-pb0)*pb1*      quarter
    + (1%r-pa0)*pa1*pb0*(1%r-pb1)*            quarter
    + (1%r-pa0)*pa1*(1%r-pb0)*pb1*            quarter
    + (1%r-pa0)*pa1*(1%r-pb0)*(1%r-pb1)*      quarter
    + (1%r-pa0)*(1%r-pa1)*pb0*pb1*            quarter
    + (1%r-pa0)*(1%r-pa1)*pb0*(1%r-pb1)*      quarter
    + (1%r-pa0)*(1%r-pa1)*(1%r-pb0)*pb1*      quarter
    + (1%r-pa0)*(1%r-pa1)*(1%r-pb0)*(1%r-pb1)*quarter.

    cut failpoly_explicit_eq: failpoly_explicit = failpoly pa0 pa1 pb0 pb1.
        by rewrite /failpoly_explicit /failpoly /failprob1; smt.

    cut split_leq: forall (a b c d:real), c <= d => a <= b => a+c <= b+d. by smt.
    cut split_leq2: forall (a b c:real), a >= 0%r => b <= c => a*b <= a*c. by smt.
    cut split_leq3: forall (a b:real), 0%r <= b => 0%r <= a => 0%r <= a*b. by smt.
    cut aux1: forall (a:real), a <= 1%r => 0%r <= 1%r - a. by smt.

    cut failpoly_explicit_geq: failpoly_explicit >= failpoly_quarter.
      rewrite /failpoly_quarter /failpoly_explicit.
      clear failpoly_explicit_eq failpoly_explicit failpoly_quarter.
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    apply split_leq. by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).
    by do (apply split_leq2 || (apply split_leq3 || (apply aux1 || apply pure))).

    clear split_leq split_leq2 split_leq3 aux1.

    cut failpoly_quarter_eq: failpoly_quarter = quarter.
      rewrite /failpoly_quarter. smt.
    
    rewrite -failpoly_quarter_eq -failpoly_explicit_eq.
    exact failpoly_explicit_geq.
qed.

(* Simple corollary from xyab_prob2 and failpoly_bound: 
   The probability that A and B lose is at least 1/4.
*)
local lemma xyab_prob3 pa0 pa1 pb0 pb1 (globs:glob A*glob B) &m:
    (glob A){m} = globs.`1 =>
    (glob B){m} = globs.`2 =>
    pa0 = Pr[A.invoke(false) @ &m : res = true] =>
    pa1 = Pr[A.invoke(true) @ &m : res = true] =>
    pb0 = Pr[B.invoke(false) @ &m : res = true] =>
    pb1 = Pr[B.invoke(true) @ &m : res = true] =>
    phoare [ C.xyab : (glob A) = globs.`1 /\ (glob B) = globs.`2 ==> 
      lose C.x C.y C.a C.b ] >= quarter.
proof.
  move => globA globB Hpa0 Hpa1 Hpb0 Hpb1.
  cut bounds:(pa0<=1%r /\ pa0>=0%r /\ pa1<=1%r /\ pa1>=0%r /\
              pb0<=1%r /\ pb0>=0%r /\ pb1<=1%r /\ pb1>=0%r).
    by rewrite Hpa0 Hpa1 Hpb0 Hpb1; do split; byphoare => //.
  conseq (_: _==>_: =(failpoly pa0 pa1 pb0 pb1)).
    by move => &hr H; apply failpoly_bound; smt.
  apply (xyab_prob2 pa0 pa1 pb0 pb1 globs &m) => //.
qed.

(* The probability that A and B lose is at least 1/4.

   The difference to xyab_prob3 is: In xyab_prob3, we considered a game where x,y are random, 
   but the initial state of A,B is fixed. (I.e., we omitted the invocation of S.) 
   In the present lemma, we consider the complete CHSH game.
*)
local lemma chsh1 &m: Pr[C.run() @ &m : res=false] >= (1%r/4%r).
    byphoare; trivial.
    clear &m.
    proc.

    seq 1: (true) (1%r) (1%r/4%r) _ 0%r; trivial.
    conseq (_: _ ==> _: =1%r); try by auto.
      by call (_:true) => //; apply lossless_S => //.

    conseq (_: exists (globs:glob A * glob B), (glob A)=globs.`1 /\ (glob B)=globs.`2 ==> _); first by smt. 
    elim * => globs.
    apply protect; case (exists &m, (glob A){m}=globs.`1 /\ (glob B){m}=globs.`2); rewrite/protect => Hexm.
    elim Hexm; move => &m [globA globB]. 
    pose pa0 := Pr[A.invoke(false) @ &m : res=true].
    pose pa1 := Pr[A.invoke(true) @ &m : res=true].
    pose pb0 := Pr[B.invoke(false) @ &m : res=true].
    pose pb1 := Pr[B.invoke(true) @ &m : res=true].
    call (_: (glob A) = globs.`1 /\ (glob B) = globs.`2 ==> 
      lose C.x C.y C.a C.b).
    by apply (xyab_prob3 pa0 pa1 pb0 pb1 globs &m) => //.
    by auto; smt.

call (_: (glob A) = globs.`1 /\ (glob B) = globs.`2 ==> true).
  by bypr; smt.
  by auto; smt.
qed.


(* An auxiliary module. It is used as a proof trick in lemma s_frame to be able to refer
   to the variables of S,A,B jointly as glob Container.
 *)
local module Container = {
  module S = S
  module A = A
  module B = B
  proc setup = S.setup
}.

(* An auxiliary lemma, stating that if all variables of A,B,S are the
   same on left/right side before execution of S.setup on both side,
   then the are the same after execution. 

   While EasyCrypt can solve such goals automatically if we only
   consider the variables of S, the fact that the variables of S,A,B
   are not disjoint makes EasyCrypt's tactic fail. This is remedied by
   packaging all of S,A,B inside an intermediate module Container and then
   using EasyCrypt's call tactic on that module.
*)
lemma s_frame: equiv [ S.setup ~ S.setup : ={glob S} /\ ={glob A} /\ ={glob B} ==> ={glob S} /\ ={glob A} /\ ={glob B} ].
  cut H: forall (Cnt<:Setup), equiv [ Cnt.setup ~ Cnt.setup : ={glob Cnt} ==> ={glob Cnt} ].
    by move => Cnt; proc*; call (_:true) => //.
  conseq [-frame] (_: ={glob Container} ==> ={glob Container}) => //. 
    
  exact (H Container).
qed.

(* Shows that the probability that A and B win is at most 3/4.

   The difference to lemma chsh1 is that now we use the module
   CHSH(S,A,B) instead of C (which does essentially the same, but
   breaks things down into different helper procedures), and that we
   talk about the winning probability instead of the losing
   probability.
 *)
lemma chsh2 &m: Pr[CHSH(S,A,B).run() @ &m : res=true] <= (3%r/4%r).
proof.
    cut Heq: Pr[CHSH(S,A,B).run() @ &m : res=true] = Pr[C.run() @ &m : !(res=false)].
    byequiv => //. 
    proc.
    inline C.xyab C.ab.
    call (_:true).
    call (_:true).
    rnd.
    rnd.
    conseq [-frame] (_: ={glob S} /\ ={glob A} /\ ={glob B} ==> ={glob S} /\ ={glob A} /\ ={glob B});
      [ smt | smt | by call s_frame ]. 

  rewrite Heq.
  rewrite Pr [mu_not].
  cut C_lossless: Pr[C.run() @ &m : true] = 1%r.
    byphoare => //; proc; inline C.xyab C.ab.
    call (_:true); first by apply lossless_B.
    call (_:true); first by apply lossless_A.
    rnd; rnd.
    call (_:true); first by apply lossless_S.
    by auto; smt.
  rewrite C_lossless.
  apply minus_leq.
  cut H: 1%r-3%r/4%r = 1%r/4%r.
    by algebra.
  rewrite H.
    print chsh1.
  exact (chsh1 &m).
qed.
   are now explicitly stated in the lemma.
 *)
lemma chsh (S<:Setup) (A<:Player) (B<:Player{A}) &m: 
    islossless S.setup =>
    islossless A.invoke =>
    islossless B.invoke =>
    Pr[CHSH(S,A,B).run() @ &m : res=true] <= (3%r/4%r).

proof.
move => s a b.
by exact (chsh2 S A B s a b &m).
qed.
