(* working title C++ *)

Require Import String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import FunctionalExtensionality.

(* Syntax *)
Inductive type : Type :=
  | T_Int : type              (* int *)
  | T_Bool : type             (* bool *)
  | T_Class : string -> type  (* C *)
  | T_Ptr : type -> type.     (* T* *)

Inductive expr : Type :=
  | Ex_Var : string -> expr                                (* x *)
  | Ex_Field_Access : expr -> string -> expr               (* e.f *)
  | Ex_Method_Call : expr -> string -> list expr -> expr   (* e.m(e_bar) *)
  | Ex_New : string -> list expr -> expr                   (* new C(e_bar) *)
  | Ex_Cast : type -> expr -> expr                         (* (C)e *)
  | Ex_Deref : expr -> expr                                (* *e *)
  | Ex_Ref : expr -> expr                                  (* &e *)
  | Ex_Seq : expr -> expr -> expr                          (* e;e *)
  | Ex_Asgn : string -> expr -> expr.                      (* T x := e *)

Inductive method : Type :=
  | Method : string -> list (type * string) -> expr -> method.

Inductive class : Type :=
  | Class : string -> string -> list (type * string) -> list method -> class.

(* Evaluation *)
Inductive value : Type :=
  | V_Int : nat -> value
  | V_Bool : bool -> value
  | V_Object : class -> value
  | V_Mem_Loc : nat -> value.

Definition env := string -> option nat.
Definition st := nat -> option value.
Definition empty_env : env := fun _ => None.
Definition empty_st : st := fun _ => None.

Definition update_env (e : env) (x : string) (n : nat) : env :=
  fun f => if String.eqb x f then Some n else e f.

Definition update_st (s : st) (n : nat) (v : value) : st :=
  fun f => if Nat.eqb n f then Some v else s f.

Definition is_used (s : st) (n : nat) : bool :=
  match s n with
  | Some _ => true
  | None => false
  end.

Fixpoint find_next_loc (s : st) (curr : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => curr
  | S fuel' => 
      if is_used s curr
      then find_next_loc s (S curr) fuel'
      else curr
  end.

Definition next_free_location (s : st) : nat :=
  find_next_loc s 0 1000.

Example test_next_loc:
  let s1 := update_st empty_st 0 (V_Int 564) in
  let s2 := update_st s1 1 (V_Bool true) in
  next_free_location s2 = 2.
Proof.
  reflexivity.
Qed.

Example test_next_loc_multi:
  let s1 := update_st empty_st 0 (V_Int 746) in
  let s2 := update_st s1 1 (V_Bool true) in
  let s3 := update_st s2 2 (V_Int 476) in
  next_free_location s3 = 3.
Proof.
  reflexivity.
Qed.

Reserved Notation "'<<' e , env , st '>>' '~>' '<<' v , env' , st' '>>'" (at level 40).

Inductive eval : expr -> env -> st -> value -> env -> st -> Prop :=
  | E_Asgn_Existing : forall x e v env st st' mem_loc,
      env x = Some mem_loc ->
      << e, env, st >> ~> << v, env, st' >> ->
      << Ex_Asgn x e, env, st >> ~> << v, env, update_st st' mem_loc v >>
  | E_Asgn_New : forall x e v env st st' new_loc,
      env x = None ->
      new_loc = next_free_location st ->
      << e, env, st >> ~> << v, env, st' >> ->
      << Ex_Asgn x e, env, st >> ~> << v, update_env env x new_loc, update_st st' new_loc v >>
  | E_Var : forall x env st mem_loc v,
      env x = Some mem_loc ->
      st mem_loc = Some v ->
      << Ex_Var x, env, st >> ~> << v, env, st >>
  | E_Deref : forall e env st v mem_loc,
      << e, env, st >> ~> << V_Mem_Loc mem_loc, env, st >> ->
      st mem_loc = Some v ->
      << Ex_Deref e, env, st >> ~> << v, env, st >>
  | E_Ref : forall x env st mem_loc,
      env x = Some mem_loc ->
      << Ex_Ref (Ex_Var x), env, st >> ~> << V_Mem_Loc mem_loc, env, st >>

where "'<<' e , env , st '>>' '~>' '<<' v , env' , st' '>>'" := (eval e env st v env' st').

Example test_asgn_new:
  let initial_env := update_env empty_env "some_val" 0 in 
  let initial_st := update_st empty_st 0 (V_Int 95) in
  << Ex_Asgn "x" (Ex_Var "some_val"), initial_env, initial_st >> ~>
  << V_Int 95, update_env initial_env "x" 1, update_st initial_st 1 (V_Int 95) >>.
Proof.
  eapply E_Asgn_New. simpl. reflexivity. simpl. reflexivity. eapply E_Var. simpl. reflexivity. simpl. reflexivity.
Qed.

Example test_asgn_existing_same:
  let initial_env := update_env empty_env "x" 0 in 
  let initial_st := update_st empty_st 0 (V_Int 68) in
  << Ex_Asgn "x" (Ex_Var "x"), initial_env, initial_st >> ~>
  << V_Int 68, initial_env, update_st initial_st 0 (V_Int 68) >>.
Proof.
  eapply E_Asgn_Existing. simpl. reflexivity. eapply E_Var. simpl. reflexivity. simpl. reflexivity.
Qed.

Example test_asgn_existing_different:
  let initial_env := update_env (update_env empty_env "x" 0) "y" 1 in 
  let initial_st := update_st (update_st empty_st 0 (V_Int 68)) 1 (V_Int 1000) in
  << Ex_Asgn "y" (Ex_Var "x"), initial_env, initial_st >> ~>
  << V_Int 68, initial_env, update_st initial_st 1 (V_Int 68) >>.
Proof.
  eapply E_Asgn_Existing. simpl. reflexivity. eapply E_Var. simpl. reflexivity. simpl. reflexivity.
Qed.

Example test_var_lookup:
  let env := update_env empty_env "x" 1 in
  let st := update_st empty_st 1 (V_Int 78) in
  << Ex_Var "x", env, st >> ~> << V_Int 78, env, st >>.
Proof.
  simpl. eapply E_Var. reflexivity. reflexivity.
Qed.

Example test_ref:
  let env := update_env empty_env "x" 1 in
  let st := update_st empty_st 1 (V_Int 89) in
  << Ex_Ref (Ex_Var "x"), env, st >> ~> << V_Mem_Loc 1, env, st >>.
Proof.
  simpl. apply E_Ref. reflexivity.
Qed.

Example test_deref:
  let env := update_env empty_env "x" 1 in
  let st := update_st empty_st 1 (V_Int 460) in
  << Ex_Deref (Ex_Ref (Ex_Var "x")), env, st >> ~> << V_Int 460, env, st >>.
Proof.
  simpl. eapply E_Deref. eapply E_Ref. reflexivity. unfold update_st. simpl. reflexivity.
Qed.

Example test_ref_deref:
  let env := update_env empty_env "x" 1 in
  let st := update_st empty_st 1 (V_Int 233) in
  << Ex_Deref (Ex_Ref (Ex_Var "x")), env, st >> ~> << V_Int 233, env, st >>.
Proof.
  simpl. eapply E_Deref. apply E_Ref. reflexivity. reflexivity.
Qed.

Theorem eval_deterministic : forall e env st v1 env1 st1 v2 env2 st2,
  << e, env, st >> ~> << v1, env1, st1 >> ->
  << e, env, st >> ~> << v2, env2, st2 >> ->
  v1 = v2 /\ env1 = env2 /\ st1 = st2.
Proof.
  intros e env st v1 env1 st1 v2 env2 st2 E1 E2.
  generalize dependent v2.
  generalize dependent env2.
  generalize dependent st2.
  induction E1; intros st2 env2 v2 E2;
  inversion E2; subst; clear E2.
  - assert (mem_loc = mem_loc0) by congruence; subst.
    eapply IHE1 in H8.
    destruct H8 as [Hv [Henv Hst]]; subst.
    split. reflexivity. split. reflexivity. reflexivity.
  - rewrite H in H2. discriminate.
  - apply (IHE1 st'0 env2 v2) in H9.
    destruct H9 as [Hv [Henv Hst]]; subst.
    split. reflexivity. split. congruence. congruence.
  - apply (IHE1 st'0 env0 v2) in H10.
    destruct H10 as [Hv [Henv Hst]]; subst.
    split. reflexivity. split. reflexivity. reflexivity.
  - assert (v = v2) by congruence; subst.
    split. reflexivity. split. reflexivity. reflexivity.
  - eapply IHE1 in H1.
    destruct H1 as [Hv [Henv Hst]].
    injection Hv as Heq; subst.
    rewrite H2 in H.
    injection H as Heq; subst.
    split. reflexivity. split. reflexivity. reflexivity.
  - assert (mem_loc = mem_loc0) by congruence; subst.
    split. reflexivity. split. reflexivity. reflexivity.
Qed.

(* Typing *)
Definition gamma := list (string * type).

Fixpoint check_type (x: string) (g: gamma) : option type :=
  match g with
  | [] => None
  | (y, t) :: rest => if string_dec x y then Some t else check_type x rest
  end.

Inductive is_of_type (g: gamma) : expr -> type -> Prop :=
  | Ty_Asgn : forall x e T,
      check_type x g = Some T ->
      is_of_type g e T ->
      is_of_type g (Ex_Asgn x e) T
  | Ty_Var : forall x T,
      check_type x g = Some T ->
      is_of_type g (Ex_Var x) T
  | Ty_Seq : forall e1 e2 T1 T2,
      is_of_type g e1 T1 ->
      is_of_type g e2 T2 ->
      is_of_type g (Ex_Seq e1 e2) T2
  | Ty_Deref : forall e T,
      is_of_type g e (T_Ptr T) ->
      is_of_type g (Ex_Deref e) T
  | Ty_Ref : forall e T,
      is_of_type g e T ->
      is_of_type g (Ex_Ref e) (T_Ptr T).

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition gamma_ex : gamma := 
  [(X, T_Int); 
   (Y, T_Ptr T_Int);
   (Z, T_Bool)].

Example type_works :
  is_of_type gamma_ex (Ex_Var X) T_Int.
Proof.
  apply Ty_Var. simpl. reflexivity.
Qed.

Example type_works_deref :
  is_of_type gamma_ex (Ex_Deref (Ex_Var Y)) T_Int.
Proof.
  apply Ty_Deref. apply Ty_Var. simpl. reflexivity.
Qed.