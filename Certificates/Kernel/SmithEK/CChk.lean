module

public import Certificates.Data.Kernel.SmithEKC
public import Certificates.Kernel.SmithEK.Cols
public import Certificates.Kernel.UnitarySix.Tables

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

@[expose] noncomputable def cctTreeE (R : Nat → Nat) (E : Nat) :
    List Nat → List Nat → List Nat → Nat → Bool :=
  fun J => List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool)
    (fun _ _ K => Nat.beq K E)
    (fun j _ ih G P K => (cctBit K (G.headD 0) && cctBit K (P.headD 0) &&
      Nat.beq (cctFld (R (G.headD 0)) (P.headD 0)) j &&
      cctCmp (R (G.headD 0)) (R (P.headD 0)) 693 (R j) (R (G.headD 0))) &&
      ih G.tail P.tail (Nat.lor K (Nat.shiftLeft 1 j))) J

@[expose] noncomputable def cctHeadC (C : List (List Nat)) : Bool :=
  C.length == 693 && C.all (fun c => c.length == 20 && c.all fun x => decide (x < 2 ^ 20))

@[expose] noncomputable def cctGenC (C : List (List Nat)) (R : Nat → Nat) (Gs : List Nat) : Bool :=
  let REP := pkW 400 (List.replicate 693 1)
  let Q := C.map (pkW 20)
  cctGen (REP * l20) REP (pkW 20 ((List.range 20).map (2 ^ ·))) (pkW 400 Q) (qsOf C) C R Gs

theorem cctTreeE_tail_drop (G : List Nat) (n : Nat) : G.tail.drop n = G.drop (n + 1) := by
  cases G with
  | nil => simp
  | cons a G => rfl

theorem cctTreeE_split0 {R : Nat → Nat} {E M : Nat} : ∀ (n : Nat) (J G P : List Nat) (K : Nat),
    cctTreeE R M (J.take n) G P K = true →
    cctTreeE R E (J.drop n) (G.drop n) (P.drop n) M = true → cctTreeE R E J G P K = true
  | 0, J, G, P, K, h1, h2 => by
    have h1' : Nat.beq K M = true := h1
    rw [Nat.beq_eq] at h1'
    subst h1'
    exact h2
  | n + 1, [], G, P, K, h1, h2 => by
    have h1' : Nat.beq K M = true := h1
    have h2' : Nat.beq M E = true := h2
    rw [Nat.beq_eq] at h1'
    subst h1'
    exact h2'
  | n + 1, j :: J, G, P, K, h1, h2 => by
    have h1' : ((cctBit K (G.headD 0) && cctBit K (P.headD 0) &&
        Nat.beq (cctFld (R (G.headD 0)) (P.headD 0)) j &&
        cctCmp (R (G.headD 0)) (R (P.headD 0)) 693 (R j) (R (G.headD 0))) &&
        cctTreeE R M (J.take n) G.tail P.tail (Nat.lor K (Nat.shiftLeft 1 j))) = true := h1
    rw [Bool.and_eq_true] at h1'
    have h2' : cctTreeE R E (J.drop n) (G.tail.drop n) (P.tail.drop n) M = true := by
      rw [cctTreeE_tail_drop G, cctTreeE_tail_drop P]
      exact h2
    change ((cctBit K (G.headD 0) && cctBit K (P.headD 0) &&
        Nat.beq (cctFld (R (G.headD 0)) (P.headD 0)) j &&
        cctCmp (R (G.headD 0)) (R (P.headD 0)) 693 (R j) (R (G.headD 0))) &&
        cctTreeE R E J G.tail P.tail (Nat.lor K (Nat.shiftLeft 1 j))) = true
    rw [Bool.and_eq_true]
    exact ⟨h1'.1, cctTreeE_split0 n J G.tail P.tail _ h1'.2 h2'⟩

theorem cctTreeE_split {R : Nat → Nat} {E M : Nat} (a n : Nat) {J G P : List Nat} {K : Nat}
    (h1 : cctTreeE R M ((J.drop a).take n) (G.drop a) (P.drop a) K = true)
    (h2 : cctTreeE R E (J.drop (a + n)) (G.drop (a + n)) (P.drop (a + n)) M = true) :
    cctTreeE R E (J.drop a) (G.drop a) (P.drop a) K = true := by
  refine cctTreeE_split0 n _ _ _ K h1 ?_
  simp only [List.drop_drop]
  exact h2

theorem chkCTree_intro {C : List (List Nat)} {R : Nat → Nat} (h0 : cctHeadC C = true)
    (hg : cctGenC C R cctGens = true)
    (ht : cctTreeE R (Nat.sub (Nat.shiftLeft 1 693) 1) (cctJ.drop 0) (cctG.drop 0) (cctP.drop 0)
      (cctMask cctGens) = true) :
    chkCTree C R = true := by
  have e : chkCTree C R = ((cctHeadC C && cctGenC C R cctGens) &&
      cctTreeE R (Nat.sub (Nat.shiftLeft 1 693) 1) cctJ cctG cctP (cctMask cctGens)) := rfl
  have ht' : cctTreeE R (Nat.sub (Nat.shiftLeft 1 693) 1) cctJ cctG cctP (cctMask cctGens) =
    true := ht
  rw [e, h0, hg, ht']
  rfl

open CertificateChecks.KernelU6.T (R)

theorem c21260conj_hd : cctHeadC cs.L = true := by decide +kernel

theorem c21260conj_gen : cctGenC cs.L R cctGens = true := by decide +kernel

theorem c21260conj_t0 : cctTreeE R (cctMask (cctGens ++ cctJ.take 100))
    ((cctJ.drop 0).take 100) (cctG.drop 0) (cctP.drop 0) (cctMask cctGens) = true := by
  decide +kernel
theorem c21260conj_t1 : cctTreeE R (cctMask (cctGens ++ cctJ.take 200))
    ((cctJ.drop 100).take 100) (cctG.drop 100) (cctP.drop 100)
    (cctMask (cctGens ++ cctJ.take 100)) = true := by
  decide +kernel
theorem c21260conj_t2 : cctTreeE R (cctMask (cctGens ++ cctJ.take 300))
    ((cctJ.drop 200).take 100) (cctG.drop 200) (cctP.drop 200)
    (cctMask (cctGens ++ cctJ.take 200)) = true := by
  decide +kernel
theorem c21260conj_t3 : cctTreeE R (cctMask (cctGens ++ cctJ.take 400))
    ((cctJ.drop 300).take 100) (cctG.drop 300) (cctP.drop 300)
    (cctMask (cctGens ++ cctJ.take 300)) = true := by
  decide +kernel
theorem c21260conj_t4 : cctTreeE R (cctMask (cctGens ++ cctJ.take 500))
    ((cctJ.drop 400).take 100) (cctG.drop 400) (cctP.drop 400)
    (cctMask (cctGens ++ cctJ.take 400)) = true := by
  decide +kernel
theorem c21260conj_t5 : cctTreeE R (cctMask (cctGens ++ cctJ.take 600))
    ((cctJ.drop 500).take 100) (cctG.drop 500) (cctP.drop 500)
    (cctMask (cctGens ++ cctJ.take 500)) = true := by
  decide +kernel
theorem c21260conj_t6 : cctTreeE R (Nat.sub (Nat.shiftLeft 1 693) 1)
    (cctJ.drop 600) (cctG.drop 600) (cctP.drop 600)
    (cctMask (cctGens ++ cctJ.take 600)) = true := by
  decide +kernel

theorem c21260conj : chkCTree cs.L R = true :=
  chkCTree_intro c21260conj_hd
    c21260conj_gen
    (cctTreeE_split 0 100 c21260conj_t0 <| cctTreeE_split 100 100 c21260conj_t1 <|
      cctTreeE_split 200 100 c21260conj_t2 <| cctTreeE_split 300 100 c21260conj_t3 <|
      cctTreeE_split 400 100 c21260conj_t4 <| cctTreeE_split 500 100 c21260conj_t5 <|
      c21260conj_t6)

end CertificateChecks.KernelSmithEK
