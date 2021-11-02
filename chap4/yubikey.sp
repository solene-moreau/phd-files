(*******************************************************************************
YUBIKEY

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model’, 2014.

Y -> S : <pid,<nonce,otp>>
S -> Y : ok

COMMENTS
- otp is an encryption of a triple (secret(i), cpt(i), npr(i,j)), modelled here
as a randomized encryption

PROOFS 
- counterIncrease
- noReplay
- monotonicity
- injective correspondence

*******************************************************************************)

set autoIntro = false.

senc enc,dec

abstract startplug: message
abstract endplug: message
abstract startpress: message
abstract accept:message
abstract myzero: message
abstract myone: message

abstract mySucc : message->message

abstract pid : index -> message
name k: index -> message
name secret: index -> message
name nonce: index->index->message
name npr: index->index->message

(* counter value on the Yubikey side *)
mutable YCpt(i:index): message = myzero
(* counter value on the server side *)
mutable SCpt(i:index): message = myzero

channel cT
channel cR

abstract orderOk : message
abstract order : message->message->message

(* When the key is plugged, its counter is incremented *)
process yubikeyplug(i:index,j:index) =
  in(cT, x1);
  if x1 = startplug then YCpt(i) := mySucc(YCpt(i)); out(cT,endplug)

(* When the key is pressed, an otp is sent with the current value of the counter,
and the counter is incremented *)
process yubikeypress(i:index,j:index) =
  in(cT,x2);
  if x2 = startpress then
    let cpt = YCpt(i) in
    YCpt(i) := mySucc(YCpt(i));
    out(cT,<pid(i),<nonce(i,j),enc(<secret(i),cpt>,npr(i,j),k(i))>>)

(* When the server receives a message, it checks whether it corresponds to a pid
in its database, and checks also that the counter inside the otp is strictly 
greater than the counter associated to the token. 
If so, the value inside the otp is used to update the database.
Now, the counter value associated to this token is this new value. *)
process server(ii:index) =
  in(cR,y1);
  try find i such that fst(y1) = pid(i) in
    if dec(snd(snd(y1)),k(i)) <> fail 
        && order(SCpt(i),snd(dec(snd(snd(y1)),k(i)))) = orderOk 
    then
      SCpt(i) := snd(dec(snd(snd(y1)),k(i)));
      out(cR,accept)

system 
  ( (!_i !_j Plug: yubikeyplug(i,j)) 
    | (!_i !_j Press: yubikeypress(i,j)) 
    | (!_ii S: server(ii))).

axiom orderTrans :
  forall (n1,n2,n3:message),
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
      => order(n1,n3) = orderOk

axiom orderStrict : 
  forall (n1,n2:message), n1 = n2 => order(n1,n2) <> orderOk.
  
(* The counter SCpt(i) strictly increases when t is an action S performed by 
the server with tag i. *)
goal counterIncreaseStrictPred:
  forall (ii,i:index), happens(S(ii,i)) =>
    (cond@S(ii,i) => order(SCpt(i)@pred(S(ii,i)),SCpt(i)@S(ii,i)) = orderOk).
Proof.
  intro ii i Hap Hcond.
  expand cond@S(ii,i).
  destruct Hcond as [Mneq Morder Meq].
  expand SCpt(i)@S(ii,i).
  assumption.
Qed.

(* The counter SCpt(i) increases (not strictly) between pred(t) and t. *)
goal counterIncreasePred:
  forall (t:timestamp), happens(t) =>
    (forall (i:index),
      (t > init && exec@t) =>
        (order(SCpt(i)@pred(t),SCpt(i)@t) = orderOk 
        || SCpt(i)@t = SCpt(i)@pred(t))).
Proof.
  intro t Hap i [Ht Hexec].
  case t; 2,3,4,5,7,8: simpl_left; expand SCpt(i)@t; auto.

  auto.

  destruct H as [ii i0 H].
  assert (i = i0 || i <> i0) as Hi. auto.
  case Hi.
    (* i = i0 *)
    left. subst t, S(ii,i).
    expand exec@S(ii,i).
    by use counterIncreaseStrictPred with ii, i.
    (* i <> i0 *)
    right. subst t, S(ii,i0).
    case 
      (if i = i0 then snd(dec(snd(snd(input@S(ii,i0))),k(i0))) 
       else SCpt(i)@pred(S(ii,i0))).
    auto.
    expand SCpt(i)@S(ii,i0).
    case 
      (if i = i0 then snd(dec(snd(snd(input@S(ii,i0))),k(i0))) 
       else SCpt(i)@pred(S(ii,i0))); 1,2: auto.
Qed.

(* The counter SCpt(i) increases (not strictly) between t' and t when t' < t *)
goal counterIncrease:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
      ((exec@t && t' < t) =>
        (order(SCpt(i)@t',SCpt(i)@t) = orderOk || SCpt(i)@t = SCpt(i)@t')).
Proof.
  induction.
  intro IH0 t' i Hap [Hexec Ht'].
  assert (t' = pred(t) || t' < pred(t)) as H0; 1: by case t. 
  case H0.

  (* case t' = pred(t) *)
  use counterIncreasePred with t as H1; 2: assumption.
  use H1 with i as H2; 2: auto.
  subst pred(t), t'.
  assumption.

  (* case t' < pred(t) *)
  use IH0 with pred(t),t',i as H1; 2,3: auto.
  use counterIncreasePred with t as H2; 2: assumption.
  use H2 with i as H3.
  case H1.
    (* case H1 - 1/2 *)
    case H3.
      left.
      use orderTrans with SCpt(i)@t',SCpt(i)@pred(t),SCpt(i)@t.
      congruence.
      split; 1,2: assumption.
      left; congruence.
    (* case H1 - 2/2 *)
    case H3.
      left; congruence.
      right; congruence.

      split; 1,2: auto.
      executable t; 1,2: assumption.
      intro H1.
      use H1 with pred(t) as H2; 2: auto.
      split; 1,2: auto.
Qed.


goal noReplayInvariant:
  forall (ii, ii1, i:index), happens(S(ii1,i),S(ii,i)) =>
    (exec@S(ii1,i) && S(ii,i) < S(ii1,i)
      => order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk).
Proof.
  intro ii ii1 i Hap [Hexec Ht].
  use counterIncreaseStrictPred with ii1, i as M0; 2: auto.
  assert (S(ii,i) = pred(S(ii1,i)) || S(ii,i) < pred(S(ii1,i))) as H1.
  constraints.
  case H1.
    (* case S(ii,i) = pred(S(ii1,i)) *)
    congruence.
    (* case S(ii,i) < pred(S(ii1,i)) *)
    use counterIncrease with pred(S(ii1,i)),S(ii,i),i as H2; 2: auto.
    case H2.
    use orderTrans with SCpt(i)@S(ii,i), SCpt(i)@pred(S(ii1,i)),SCpt(i)@S(ii1,i); 1: auto.
    split; 1,2: assumption.
    congruence.
    split.
    executable S(ii1,i); 1,2: auto.
    intro H.
    use H with pred(S(ii1,i)) as Hexec'; 1,2: auto.
    assumption.
  expand exec@S(ii1,i).
  destruct Hexec as [Hpred Hcond].
  assumption.
Qed.

goal noReplay:
  forall (ii, ii1, i:index), happens(S(ii1,i)) =>
    (exec@S(ii1,i) && S(ii,i) <= S(ii1,i) && SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i) 
     => ii = ii1).
Proof.
  intro ii ii1 i Hap [Hexec Ht Meq].
  assert (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i)) as H1.
  constraints.
  case H1.
  (* case S(ii,i) * S(ii1,i) *) 
  constraints.
  (* case S(ii,i) < S(ii1,i) *)
  use noReplayInvariant with ii, ii1, i as M1; 2: auto.
  use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i); 1,2: auto.
  split; 1,2: assumption.
Qed.


goal monotonicity:
  forall (ii, ii1, i:index), happens(S(ii1,i),S(ii,i)) =>
    (exec@S(ii1,i) && exec@S(ii,i) && 
      order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk
    => S(ii,i) < S(ii1,i)).
Proof.
  intro ii ii1 i Hap [Hexec H].
  assert
    (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i) || S(ii,i) > S(ii1,i)) as Ht.
  constraints.
  case Ht.
  (* case S(ii,i) = S(ii1,i) *)
  use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i); 1,2: congruence.
  (* case S(ii,i) < S(ii1,i) *)
  assumption.
  (* case S(ii,i) > S(ii1,i) *)
  use noReplayInvariant with ii1, ii, i as H'.
  use orderTrans with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i), SCpt(i)@S(ii,i) as H''.
  use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i) as Mneq; 1,2: congruence.
  split; 1,2: assumption.
  split; 1,2: constraints.
  split; 1,2: auto.
Qed.


goal injectiveCorrespondence:
   forall (ii,i:index), happens(S(ii,i)) =>
     (exec@S(ii,i) =>
       (exists (j:index),
       Press(i,j) < S(ii,i) && cpt(i,j)@Press(i,j) = SCpt(i)@S(ii,i)
       && (forall (ii1:index), happens(S(ii1,i)) =>
            exec@S(ii1,i) => cpt(i,j)@Press(i,j) = SCpt(i)@S(ii1,i)
              => ii1 = ii))).
Proof.
  intro ii i Hap Hexec.
  expand exec@S(ii,i).
  expand cond@S(ii,i).
  destruct Hexec as [Hpred [Mneq M1 M2]].
  intctxt Mneq; 2: intro *; congruence.
  intro Ht M3 *.
  exists j.
  split. split.
  assumption.
  expand output@Press(i,j); congruence.
  intro ii' Hap' Hexec'.
  expand exec@S(ii',i). destruct Hexec' as [Hpred' Hcond'].
  intro M4.

assert (SCpt(i)@S(ii,i) = SCpt(i)@S(ii',i)) => //.
assert (S(ii,i) = S(ii',i) || S(ii,i) < S(ii',i) || S(ii,i) > S(ii',i)) => //.
case H => //.

(* 1st case: S(ii,i) < S(ii',i) *)
assert (S(ii,i) = pred(S(ii',i)) || S(ii,i) < pred(S(ii',i))) as H0.
constraints.
case H0.

(* S(ii,i) = pred(S(ii',i) < S(ii',i) *)
use counterIncreaseStrictPred with ii',i; 2,3: auto.
subst S(ii,i), pred(S(ii',i)).
use orderStrict with SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii',i); 1,2: auto.

(* S(ii,i) < pred(S(ii',i))  < S(ii',i) *)
use counterIncreaseStrictPred with ii',i; 2,3: auto.
use counterIncrease with pred(S(ii',i)), S(ii,i), i; 2,3: auto.
case H.

use orderTrans with SCpt(i)@S(ii,i), SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii',i); 2: auto.
use orderStrict with SCpt(i)@S(ii,i), SCpt(i)@S(ii',i); 2: auto.
auto.
subst SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii,i).
use orderStrict with SCpt(i)@S(ii,i), SCpt(i)@S(ii',i); auto.

(* 2nd case: S(ii,i) > S(ii',i) *)
assert (pred(S(ii,i)) = S(ii',i) || pred(S(ii,i)) > S(ii',i)) as H0.
constraints.
case H0.

(* S(ii,i) > pred(S(ii,i)) = S(ii',i) *)
use counterIncreaseStrictPred with ii,i; 2: auto.
subst S(ii',i), pred(S(ii,i)).
use orderStrict with SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii,i); 2: auto.
auto.
expand cond@S(ii,i).
split.
split.
assumption.
assumption.
assumption.

(* S(ii,i) > pred(S(ii,i)) >  S(ii',i) *)
use counterIncreaseStrictPred with ii,i; 2: auto.
use counterIncrease with pred(S(ii,i)), S(ii',i), i; 2,3: auto.
case H.

use orderTrans with SCpt(i)@S(ii',i), SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii,i); 2: auto.
use orderStrict with SCpt(i)@S(ii',i), SCpt(i)@S(ii,i); 2: auto.
auto.

subst SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii',i).
use orderStrict with SCpt(i)@S(ii',i), SCpt(i)@S(ii,i); auto.
expand cond@S(ii,i).
split.
split.
assumption.
assumption.
assumption.
Qed.
