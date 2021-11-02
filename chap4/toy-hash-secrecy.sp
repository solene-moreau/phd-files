(*******************************************************************************
TOY EXAMPLE WITH STATE

System with tags only.

The goal is to prove the equivalence between:
- a system outputting the updated value kT(i) hashed with key(i) (ie same key for
all sessions of identity i),
- and a system outputting a fresh name at each session.

PROOFS
- lastUpdate
- stateInequality
- equivalence between real and ideal systems
*******************************************************************************)

set autoIntro = false.

hash hkey

abstract ok : message
abstract ko : message

name key : index->message
name seed : index->message
name n : index->index->message

mutable kT(i:index) : message = seed(i)

channel cT

process tag(i:index,j:index) =
  kT(i) := hkey(kT(i),key(i));
  out(cT, diff(kT(i),n(i,j)))

system (!_i !_j T: tag(i,j)).

(* GOALS *)

(* kT(i)@t = kT(i)@t' where t' is init or the previous update of kT(i) *)
goal lastUpdate : forall (t:timestamp) forall (i:index)
  happens(t) =>
  ((kT(i)@t = kT(i)@init && forall (j':index), happens(T(i,j')) => t < T(i,j')) ||
    (exists j:index,
     kT(i)@t = kT(i)@T(i,j) &&
     T(i,j) <= t &&
     (forall (j':index), happens(T(i,j')) => (T(i,j')<=T(i,j) || t<T(i,j'))))).
Proof.
  induction.
  intro Hind i Hap.
  case t.

  (* t = init *)
  left. split.
  auto.
  intro j' Hap'.  
  auto.

  (* t = T(i0,j) *)
  destruct H as [i0 j H].
  assert (i=i0 || i<>i0) as H0. constraints.
  case H0.

  (* i=i0 *)
  subst t,T(i,j).
  right. exists j.
  split; 1,2: auto.

  (* i<>i0 *)
  subst t,T(i0,j).
  assert kT(i)@T(i0,j) = kT(i)@pred(T(i0,j)).
  expand kT(i)@T(i0,j).
  by noif.
  use Hind with pred(T(i0,j)),i as HH0; 2,3: auto.
  case HH0.
    (* case HH0 - init *)
    destruct H as [H1 H2].
    left. split.
    congruence.
    intro j' Hap'.
    use H2 with j'; 1,2: auto.
    (* case HH0 - general *)
    right. destruct H as [j0 H].
    exists j0.
    split. split. 
    congruence.
    constraints.
    intro j' Hap'.
    destruct H as [H1 H2 H3].
    use H3 with j' as H4; 2: auto. 
    case H4.
    left; assumption.
    right; constraints.
Qed.

goal stateInequality :
  forall (t,t':timestamp), forall (i,j,i':index)
     happens(t) =>
     (t = T(i,j) &&  t' < t => kT(i)@t <> kT(i')@t').
Proof.
  induction.
  intro Hind t' i j i' Hap [H1 H2] Mneq.
  subst t, T(i,j).
  expand kT(i)@T(i,j).
  euf Mneq.
  intro Ht Meq *.

  (* T(i,j0) < T(i,j)
     kT(i)@pred(T(i,j0)) = kT(i)@pred(T(i,j))
     in order to use the induction hypothesis,
     we need timestamps of the form T(i,_)
     but pred(_) has no reason to be of that form,
     this is where lastUpdate comes into play *)
  use lastUpdate with pred(T(i,j)),i as H1; 2: auto.
  case H1.

    (* case H1 - init *)
    destruct H as [H1 H1'].
    (* kT(i)@pred(T(i,j)) = kT(i)@init
       this can actually happen only if tag i has 
       not played from init to pred(T(i,j))
       but we know that T(i,j0) < T(i,j): absurd *)
    use H1' with j0; 1,2: case Ht; auto.

    (* case H1 - general *)
    simpl_left.
    (* kT(i)@pred(T(i,j)) = kT(i)@T(i,j1)
       then we should have that T(i,j0) <= T(i,j1) *)
    assert (T(i,j0) <= T(i,j1)).
      use H0 with j0 as H0'. 
      case Ht; 1,2: case H0'; auto. 
      case Ht; 1,2: auto.
    use Hind with T(i,j1),pred(T(i,j0)),i,j1,i; 1,2,3,4: auto.
Qed.

equiv realIdeal.
Proof.
  induction t.
  expand frame@T(i,j). expand exec@T(i,j). expand cond@T(i,j).
  fa 0.
  fa 1. fa 1.
  expand output@T(i,j). expand kT(i)@T(i,j).
  prf 1.
  yesif 1.
  intro i0 j0 *.
  use stateInequality with T(i,j),T(i,j0),i,j,i; 2,3: auto.
  expand kT(i)@T(i,j).
  expand kT(i)@T(i,j0).
  congruence.
  fresh 1.
  yesif 1.
  auto.
Qed.
