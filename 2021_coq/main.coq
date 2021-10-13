Section Euclidean_plane.

  Require Import Coq.Reals.Rdefinitions.
  Require Import Coq.Reals.R_sqrt.
  Require Import Coq.Reals.Rfunctions.
  Require Import Coq.Reals.Raxioms.
  Require Export Coq.Reals.RIneq.
  Open Scope R_scope.


  (*実内積空間のベクトル*)
  Inductive vector : Type.

  (*点*)
  Inductive point : Type.

  (*ベクトル加法*)
  Parameter vector_plus : vector -> vector -> vector.
  Notation "a +' b" := (vector_plus a b)
    (at level 50, left associativity). (*a +' b でベクトル a と b の加算*)

  (*スカラー乗法*)
  Parameter vector_mult : R -> vector -> vector.
  Notation "x *' a" := (vector_mult x a)
    (at level 40, left associativity). (*x *' a で実数 x とベクトル a の乗算*)

  (*内積*)
  Parameter vector_inner_product : vector -> vector -> R.
  Notation "a ・ b" := (vector_inner_product a b)
    (at level 40, left associativity). (*a ・ b で ベクトル a と b の内積*)

  (*実内積空間の公理*)
    (*実ベクトル空間の公理*)
    (*coq で扱いやすいように, 逆元, 単位元の存在ではなく, 逆元を求める関数と単位元の定数を定義する形を取った*)
    Axiom comm_add : forall (a b : vector), a +' b = b +' a.

    Axiom assoc_add : forall (a b c : vector), (a +' b) +' c = a +' (b +' c).

    Parameter v0 : vector. (* v0 はゼロベクトル*)
    Axiom exists_zero : forall (a : vector), v0 +' a = a.

    Parameter vector_opp : vector -> vector.
    Notation "-' a" := (vector_opp a)
      (at level 35, right associativity). (*-* a で a の逆元*)
    Axiom exists_opp : forall (a : vector), a +' (-' a) = v0.

    Axiom vector_comp : forall (a b : R) (c : vector), (a * b) *' c = a *' (b *' c).

    Axiom vector_ident_scalar : forall (a : vector), 1 *' a = a.

    Axiom vector_distri1 : forall (a : R) (b c : vector), a *' (b +' c) = a *' b +' a *' c.
    Axiom vector_distri2 : forall (a b : R) (c : vector), (a + b) *' c = a *' c +' b *' c.

    (*実数上の内積の公理 (定義)*)
    Axiom inner_linearity1 : forall (a : R) (b c : vector), (a *' b) ・ c = a * (b ・ c).
    Axiom inner_linearity2 : forall (a b c : vector), (a +' b) ・ c = a ・ c + b ・ c.

    Axiom inner_comm : forall (a b : vector), a ・ b = b ・ a.

    Axiom inner_pos : forall (a : vector), 0 <= a ・ a.

    Axiom inner_zero : forall (a : vector), a ・ a = 0 -> a = v0.

  (*ユークリッド空間*)
    (*現代数学では, ユークリッド空間は実内積空間を用いて定義されることが一般的である*)
    (*ref : Wikipedia 日本語版 「ユークリッド空間」*)
    (*      https://ja.wikipedia.org/wiki/%E3%83%A6%E3%83%BC%E3%82%AF%E3%83%AA%E3%83%83%E3%83%89%E7%A9%BA%E9%96%93*)
    (*内積空間, 点は既に定義したので, それを関連付ける写像 f を定義する*)
    (*ユークリッド空間は一般的に有限次元の内積空間である必要があるが, 今回はその条件を使わないので省いた*)
    Parameter f : point -> point -> vector. (*(f P Q) でベクトル PQ を得る, 一意に定まるのはこの定義で分かるので公理からは省いた*)

    Axiom Euclid_2 : forall (P Q R : point), (f P Q) +' (f Q R) = (f P R).

    Axiom Euclid_3 : forall (P : point) (a : vector), (exists ! (Q : point), (f P Q) = a).

  (*ベクトルの大きさ*)
  Definition length (a : vector) := sqrt (a ・ a).

  (*二点間の距離*)
  Definition d (P Q : point) := length (f P Q).

  (*垂直*)
  Inductive perpe (a b : vector) := 
    | perpe_intro : a ・ b = 0 -> (perpe a b).
  Notation "a ⊥ b" := (perpe a b)
      (at level 110, left associativity).


  (*補題 : ベクトル a に対し (length a) ^ 2 = a ・ a*)
    Lemma vector_length_sqr : forall (a : vector), (length a) ^ 2 = a ・ a.
      Proof.
      intros.
      unfold length.
      apply pow2_sqrt.
      apply inner_pos.
      Qed.

  Theorem Pythagorean : forall (A B C : point),
                            (((f A B) ⊥ (f B C)) ->
                               ((d A B) ^ 2 + (d B C) ^ 2 = (d A C) ^ 2)).


    Proof.
    intros.
    destruct H.
    unfold d. (* d を展開 *)
    replace (length (f A C) ^ 2) with ((f A C) ・ (f A C)).
    replace (length (f A B) ^ 2) with ((f A B) ・ (f A B)).
    replace (length (f B C) ^ 2) with ((f B C) ・ (f B C)).

    replace (f A C) with ((f A B) +' (f B C)).
    replace ((f A B +' f B C) ・ (f A B +' f B C)) with 
    ((f A B ・ (f A B +' f B C)) + ((f A B +' f B C) ・ f B C)).

    replace (f A B ・ (f A B +' f B C) + (f A B +' f B C) ・ f B C) with
    ((f A B ・ f A B) + (f A B ・ f B C) + (f A B ・ f B C) + (f B C ・ f B C)).
    replace (f A B ・ f A B + f A B ・ f B C) with (f A B ・ f A B).
    replace (f A B ・ f A B + f A B ・ f B C) with (f A B ・ f A B).
    apply refl_equal.

    replace (f A B ・ f B C) with (0).
    field.
    replace (f A B ・ f B C) with (0).
    field.
    
    replace (f A B ・ (f A B +' f B C)) with (f A B ・ f A B + f A B ・ f B C).
    replace ((f A B +' f B C) ・ f B C) with (f A B ・ f B C + f B C ・ f B C).
    field.


    replace (f A B ・ f B C + f B C ・ f B C) with ((f A B +' f B C) ・ f B C).
    apply refl_equal.
    apply inner_linearity2.

    replace (f A B ・ f A B + f A B ・ f B C) with (f A B ・ (f A B +' f B C)).
    apply refl_equal.
    replace (f A B ・ (f A B +' f B C)) with ((f A B +' f B C) ・ f A B).
    replace (f A B ・ f B C) with (f B C ・ f A B).
    apply inner_linearity2.

    apply inner_comm.

    apply inner_comm.

    replace  ((f A B +' f B C) ・ f B C) with (f B C ・ (f A B +' f B C)).
    replace (f A B ・ (f A B +' f B C) + f B C ・ (f A B +' f B C)) with
    ((f A B +' f B C) ・ (f A B +' f B C)).
    apply refl_equal.

    apply inner_linearity2.

    apply inner_comm.

    apply Euclid_2.

    replace (f B C ・ f B C) with (length (f B C) ^ 2).
    apply refl_equal.
    apply vector_length_sqr.
    replace (f A B ・ f A B) with (length (f A B) ^ 2).
    apply refl_equal.
    apply vector_length_sqr.
    replace (f A C ・ f A C) with (length (f A C) ^ 2).
    apply refl_equal.
    apply vector_length_sqr.

    Qed.
