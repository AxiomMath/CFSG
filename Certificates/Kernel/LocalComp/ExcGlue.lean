module

public import CFSG.Certificates.Kernel.LocalCompExcDerivSound
public import Certificates.Kernel.LocalQT.He4148.Glue
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound

public section

namespace CertificateChecks.KernelLC.ExcGlue

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.M11
open CFSG.KS.SporSch.CodesImg CFSG.KC.LocalComp.ExcDeriv CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Schreier.Native

variable {n w : Nat}

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem img_one (n : Nat) :
    imageList (1 : Equiv.Perm (Fin n)) = (CFSG.Monster.B.Co2.Native.idA n).toList := by
  apply List.ext_getElem <;> simp [imageList, CFSG.Monster.B.Co2.Native.idA]

theorem one_img (h : idK n w (mask w) = true) :
    imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList := by
  rw [idK_sound h]
  exact img_one n

theorem words_img {gs : List (Equiv.Perm (Fin n))} {k : Nat} (hl : gs.length = k)
    {S SI : Nat → Nat} (hsz : szOK n w = true)
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack n w (S j)).toList)
    (hp : ∀ j < gs.length, permOK n w (mask w) (n * w) (S j) (SI j) = true)
    (hid : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList)
    {ws : List (List Int)} {Ps : Nat → Nat}
    (hk : allN ws.length (fun i => bAnd(lettersK k (ws.getD i []),
      Nat.beq (wordK n w (mask w) (pidn n w) S SI (ws.getD i [])) (Ps i))) = true) :
    ∀ i < ws.length, imageList ((ws.map (evalCodes gs)).getD i 1) =
      (unpack n w (Ps i)).toList := by
  intro i hi
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec hk i hi)
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    ← List.getD_eq_getElem _ [] hi, evalCodes_img hsz hg hp hid (hl ▸ h1),
    Nat.eq_of_beq_eq_true h2]

theorem ord_all {e c : Nat} (hsz : szOK n w = true) {reps : List (Equiv.Perm (Fin n))}
    {Ps : Nat → Nat} (hr : reps.length = c)
    (hi : ∀ i < c, imageList (reps.getD i 1) = (unpack n w (Ps i)).toList)
    (hk : allN c (fun i => bAnd(canonK n w (mask w) (n * w) (Ps i),
      ordIs n w (mask w) (pidn n w) (Ps i) (e - 1))) = true) (he : 0 < e) :
    (reps.map toTable).all (ordTest n e) = true := by
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 ht
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hr'
  have hic : i < c := hr ▸ hi'
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec hk i hic)
  have himg := hi i hic
  rw [List.getD_eq_getElem _ _ hi'] at himg
  exact ordTest_of_ordIs hsz himg h1 he h2

theorem comm_all {gs : List (Equiv.Perm (Fin n))} {k : Nat} (hl : gs.length = k)
    {S : Nat → Nat} {h : Equiv.Perm (Fin n)} {H : Nat} (hsz : szOK n w = true)
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack n w (S j)).toList)
    (hh : imageList h = (unpack n w H).toList)
    (hk : allN k (fun j => Nat.beq (pcomp n w (mask w) (S j) H) (pcomp n w (mask w) H (S j))) =
      true) :
    gs.all (fun g => schreierPermEq (g * h) (h * g)) = true := by
  rw [List.all_eq_true]
  intro g hg'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have himg := hg j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  have e2 := mulK_rep hsz hh himg
  rw [← Nat.eq_of_beq_eq_true (allN_spec hk j (hl ▸ hj))] at e2
  exact schreierPermEq_of_img (mulK_rep hsz himg hh) e2

theorem all_zip_of {α β : Type} {l : List α} {m : List β} {f : α × β → Bool}
    (h : ∀ i (hl : i < l.length) (hm : i < m.length), f (l[i], m[i]) = true) :
    (l.zip m).all f = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < min l.length m.length := by simpa using hi
  rw [List.getElem_zip]
  exact h i (by omega) (by omega)

theorem derivs_all_o8 {A AI : Nat → Nat} {kA : Nat} (hsz : szOK n w = true)
    (hid : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList)
    {al : List (Equiv.Perm (Fin n))} (hlen : al.length = kA)
    (hA : ∀ j < al.length, imageList (al.getD j 1) = (unpack n w (A j)).toList)
    (hAp : ∀ j < al.length, permOK n w (mask w) (n * w) (A j) (AI j) = true)
    {okW : List ℤ → Bool} {zs : List (Equiv.Perm (Fin n))} {Z : List Nat} (hZ : Corr n w zs Z)
    {reps : List (Equiv.Perm (Fin n))} {ds : List (List (ℕ × List ℤ × ℕ))}
    {x : Equiv.Perm (Fin n)} {X : Nat} {forbid : List Nat} {c : Nat} {E : Nat → Nat}
    (hx : imageList x = (unpack n w X).toList) (hl : reps.length = c)
    (hi : ∀ i < c, imageList (reps.getD i 1) = (unpack n w (E i)).toList)
    (hk : allN c (fun i => bIf(Nat.beq (E i) X, true,
      derivK n w (mask w) (n * w) (pidn n w) A AI kA okW Z forbid (ds.getD i []) [X, E i])) =
      true) :
    (reps.zip ds).all (fun p => schreierPermEq p.1 x ||
      CFSG.ComponentClassification.RankTwoClassical.ExcO8.derivCheck al okW zs forbid [x, p.1]
        p.2) = true := by
  refine all_zip_of fun i hr hd => ?_
  have hc : i < c := hl ▸ hr
  have himg := hi i hc
  rw [List.getD_eq_getElem _ _ hr] at himg
  have h := allN_spec hk i hc
  rw [List.getD_eq_getElem _ _ hd] at h
  rw [Bool.or_eq_true]
  cases e : Nat.beq (E i) X
  · rw [e] at h
    right
    exact derivK_sound_o8 hsz hid hlen hA hAp hZ _
      (List.Forall₂.cons hx (List.Forall₂.cons himg List.Forall₂.nil)) h
  · left
    exact schreierPermEq_of_img himg (Nat.eq_of_beq_eq_true e ▸ hx)

@[expose] noncomputable def minK (f c : Nat) (Q : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => bAnd(Prod.rec (motive := fun _ => Bool)
      (fun a b => bIf(Nat.beq f a, Nat.ble b c, true)) q, ih)) Q

theorem minK_spec {f c : Nat} : ∀ {Q : List (Nat × Nat)}, minK f c Q = true →
    Q.all (fun q => f != q.1 || decide (q.2 ≤ c)) = true
  | [], _ => rfl
  | (a, b) :: Q, h => by
    obtain ⟨h1, h2⟩ := and_of_bAnd h
    rw [List.all_cons, minK_spec h2, Bool.and_true]
    change bIf(Nat.beq f a, Nat.ble b c, true) = true at h1
    cases e : Nat.beq f a
    · have hne : f ≠ a := fun h' => by rw [h', Nat.beq_refl] at e; exact Bool.false_ne_true e.symm
      simp [hne]
    · rw [e] at h1
      simp [Nat.le_of_ble_eq_true h1]

theorem permOrId_img {arr : Nat → Array Nat} {P PI : Nat → Nat} {c : Nat}
    (ha : ∀ k < c, arr k = unpack n w (P k))
    (h1 : allN c (fun k => invEqK n w (mask w) (n * w) (P k) (PI k)) = true)
    (h2 : allN c (fun k => invEqK n w (mask w) (n * w) (PI k) (P k)) = true) :
    ∀ k < c, imageList (CFSG.Sporadic.HeldB.permOrId n (arr k)) = (unpack n w (P k)).toList :=
  fun k hk => CertificateChecks.KernelLQT.He4148.imageList_of_rep
    (CertificateChecks.KernelLQT.He4148.unpack_size' _ _ _)
    (CertificateChecks.KernelLQT.He4148.unpack_facts (ha k hk) (allN_spec h1 k hk)
      (allN_spec h2 k hk)).2.1

end CertificateChecks.KernelLC.ExcGlue

end
