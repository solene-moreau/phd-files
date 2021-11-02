(*******************************************************************************
TOY-COUNTER

V. Cheval, V. Cortier, and M. Turuani,
‘A Little More Conversation, a Little Less Action, a Lot More Satisfaction:
Global States in ProVerif’,
in 2018 IEEE 31st Computer Security Foundations Symposium (CSF), Oxford,
Jul. 2018, pp. 344–358, doi: 10.1109/CSF.2018.00032.

A = in(d, i : nat); out(c, h(i, s)); out(d, i + 1)
B = in(d, i : nat); in(c, y);
    if y = h(i, s) then
      out(c, s); out(d, i + 1)
    else out(d, i + 1)

P = ! A | ! B | out(d, 0) | ! in(d, i : nat); out(d, i)

COMMENTS
- In this model, we do not use private channels since actions (input/condition/
  update/output) are atomic.
- The goal is to prove that the secret s is never leaked because B receives
  only hashes with old values of the counter.

PROOFS
- counterIncrease
- secrecy
*******************************************************************************)

set autoIntro = false.

hash h

name secret : message
name key : message

abstract error : message
abstract myZero : message

mutable d : message = myZero

channel cA
channel cB

(* mySucc function for counter *)
abstract mySucc : message->message

(* order relation for counter *)
abstract orderOk : message
abstract order : message->message->message

(* processes *)
process A =
  let m = h(<d,secret>,key) in
  d := mySucc(d);
  out(cA, m)

process B =
  in(cA,y);
  if y = h(<d,secret>,key) then
    d := mySucc(d);
    out(cB,secret)
  else
    d := mySucc(d);
    out(cB,error)

system ((!_i A) | (!_j B)).

(* AXIOMS *)

axiom orderSucc : forall (n:message), order(n,mySucc(n)) = orderOk.
axiom orderTrans :
  forall (n1,n2,n3:message),
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
    => order(n1,n3) = orderOk.
axiom orderStrict : forall (n1,n2:message), n1 = n2 => order(n1,n2) <> orderOk.

(* GOALS *)

(* The counter increases strictly at each update. *)
goal counterIncreasePred (t:timestamp): 
  t > init => order(d@pred(t),d@t) = orderOk.
Proof.
  intro t Hc.
  use orderSucc with d@pred(t).
  case t; 2,3,4: intro *; simpl_left; expand d@t; congruence.
  by eqtrace.
Qed.

(* A more general result than counterIncreasePred. *)
goal counterIncrease :
  forall (t,t':timestamp), 
    (t' < t => order(d@t',d@t) = orderOk).
Proof.
  induction.
  intro Hind t' Ht.
  assert (t' < pred(t) || t' >= pred(t)) as H0; 1: by case t. 
  case H0.

    (* case t' < pred(t) *)
    use Hind with pred(t),t' as H1; 2,3: by eqtrace.
    use counterIncreasePred with t; 2: by eqtrace.
    by use orderTrans with d@t',d@pred(t),d@t.

    (* case t' >= pred(t) *)
    assert t' = pred(t). by eqtrace.
    by use counterIncreasePred with t.
Qed.

goal secret : 
  forall (j:index), happens(B(j)) => (cond@B(j) => False).
Proof.
  intro j Hap Hcond.
  expand cond@B(j).
  euf Hcond.
  intro Ht Heq.
  assert pred(A(i)) < pred(B(j)). by eqtrace.
  use counterIncrease with pred(B(j)),pred(A(i)).
  use orderStrict with d@pred(A(i)),d@pred(B(j)); congruence.
  by eqtrace.
Qed.
