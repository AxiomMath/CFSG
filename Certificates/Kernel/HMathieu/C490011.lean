module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Kernel.HMathieu.FixTab24
public import Certificates.Data.Kernel.HMathieu.PredMisc
public import Certificates.Data.Kernel.HMathieu.PredQK
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.HMathieu.FixTabSound
import CFSG.Certificates.Kernel.HMathieu.PredQKSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C490011

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

@[expose] noncomputable def gRowS {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st' : σ)
    (rs : List (Nat × Nat)) (x i : Nat) : Bool :=
  match rs.drop i with
  | [] => true
  | r :: rest => bIf(candR m c (x + i) r.2 S,
      gAllR m upd pred k ((x + i) :: l) (appMapR S S fun s => nIf(Nat.beq s m, x + i,
        Nat.land (Nat.shiftRight r.2 (Nat.mul 8 s)) 255)) (Nat.land c r.1) st' rest
        (Nat.succ (x + i)), true)

theorem gAllR_succ_of_rows {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st : σ)
    (rs : List (Nat × Nat)) (x : Nat) (f : Nat → σ) (h0 : pred l S st = true)
    (hf : ∀ i < rs.length, upd st (x + i) = f i)
    (h : ∀ i < rs.length, gRowS m upd pred k l S c (f i) rs x i = true) :
    gAllR m upd pred (k + 1) l S c st rs x = true := by
  induction rs generalizing x f with
  | nil =>
    change bAnd(pred l S st, true) = true
    rw [h0]
  | cons r rest ih =>
    have h1 := ih (x + 1) (fun i => f (i + 1))
      (fun i hi => by
        have := hf (i + 1) (by simp; omega)
        rwa [Nat.add_assoc, Nat.add_comm 1 i])
      fun i hi => by
        have := h (i + 1) (by simp; omega)
        simpa [gRowS, Nat.add_assoc, Nat.add_comm 1 i] using this
    have hr := h 0 (by simp)
    rw [← hf 0 (by simp)] at hr
    simp only [gRowS, List.drop_zero, Nat.add_zero] at hr
    change bAnd(pred l S st, _) = true at h1
    rw [h0] at h1
    change bAnd(pred l S st, bAnd(_, _)) = true
    rw [h0]
    change bAnd(_, _) = true
    have hand : ∀ a b : Bool, bAnd(a, b) = (a && b) := fun a b => by cases a <;> rfl
    rw [hand, Bool.and_eq_true]
    exact ⟨hr, h1⟩

@[expose] noncomputable def gTl {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st : σ)
    (rs : List (Nat × Nat)) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r rest ihs y => bAnd(bIf(candR m c y r.2 S,
        gAllR m upd pred k (y :: l) (appMapR S S fun s => nIf(Nat.beq s m, y,
          Nat.land (Nat.shiftRight r.2 (Nat.mul 8 s)) 255)) (Nat.land c r.1) (upd st y) rest
          (Nat.succ y), true), ihs (Nat.succ y))) rs x

theorem gAllR_succ_eq {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st : σ)
    (rs : List (Nat × Nat)) (x : Nat) :
    gAllR m upd pred (k + 1) l S c st rs x = bAnd(pred l S st, gTl m upd pred k l S c st rs x) :=
  rfl

theorem gTl_cons {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st : σ)
    (r : Nat × Nat) (rest : List (Nat × Nat)) (x : Nat) :
    gTl m upd pred k l S c st (r :: rest) x = bAnd(bIf(candR m c x r.2 S,
      gAllR m upd pred k (x :: l) (appMapR S S fun s => nIf(Nat.beq s m, x,
        Nat.land (Nat.shiftRight r.2 (Nat.mul 8 s)) 255)) (Nat.land c r.1) (upd st x) rest
        (Nat.succ x), true), gTl m upd pred k l S c st rest (Nat.succ x)) :=
  rfl

theorem gAllR_sim {σ τ : Type} (m : Nat) (upd : σ → Nat → σ) (upd' : τ → Nat → τ)
    (pred : List Nat → List Nat → σ → Bool) (pred' : List Nat → List Nat → τ → Bool)
    (R : σ → τ → Prop) (N : Nat) (hp : ∀ l S st st', R st st' → pred l S st = pred' l S st')
    (hu : ∀ st st' y, y < N → R st st' → R (upd st y) (upd' st' y)) (k : Nat) :
    ∀ l S c st st' rs x, R st st' → x + rs.length ≤ N →
      gAllR m upd pred k l S c st rs x = gAllR m upd' pred' k l S c st' rs x := by
  induction k with
  | zero => exact fun l S _ st st' _ _ h _ => hp l S st st' h
  | succ k ihk =>
    intro l S c st st' rs x h hN
    rw [gAllR_succ_eq, gAllR_succ_eq, hp l S st st' h]
    suffices hT : gTl m upd pred k l S c st rs x = gTl m upd' pred' k l S c st' rs x by rw [hT]
    induction rs generalizing x with
    | nil => rfl
    | cons r rest ih =>
      simp only [List.length_cons] at hN
      have hN' : Nat.succ x + rest.length ≤ N := by omega
      rw [gTl_cons, gTl_cons, ih (Nat.succ x) hN',
        ihk _ _ _ (upd st x) (upd' st' x) rest (Nat.succ x) (hu st st' x (by omega) h) hN']

theorem gRowS_sim {σ τ : Type} (m : Nat) (upd : σ → Nat → σ) (upd' : τ → Nat → τ)
    (pred : List Nat → List Nat → σ → Bool) (pred' : List Nat → List Nat → τ → Bool)
    (R : σ → τ → Prop) (N : Nat) (hp : ∀ l S st st', R st st' → pred l S st = pred' l S st')
    (hu : ∀ st st' y, y < N → R st st' → R (upd st y) (upd' st' y)) (k : Nat) (l S : List Nat)
    (c : Nat) (st : σ) (st' : τ) (rs : List (Nat × Nat)) (x i : Nat) (h : R st st')
    (hN : x + rs.length ≤ N) :
    gRowS m upd pred k l S c st rs x i = gRowS m upd' pred' k l S c st' rs x i := by
  unfold gRowS
  split
  · rfl
  · rename_i r rest hd
    have hl := congrArg List.length hd
    simp only [List.length_drop, List.length_cons] at hl
    rw [gAllR_sim m upd upd' pred pred' R N hp hu k _ _ _ st st' rest (Nat.succ (x + i)) h
      (by omega)]

@[expose] noncomputable def dropLtK (a : Nat) (bs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun b rest ih => Bool.rec (motive := fun _ => List Nat) (b :: rest) ih (Nat.blt b a)) bs

@[expose] noncomputable def mergeFK (as bs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun a _ ih bs => List.rec (motive := fun _ => List Nat) []
      (fun b rest _ => Bool.rec (motive := fun _ => List Nat) (ih (b :: rest)) (a :: ih rest)
        (Nat.beq a b)) (dropLtK a bs)) as bs

theorem dropLtK_cons (a b : Nat) (bs : List Nat) :
    dropLtK a (b :: bs) = if b < a then dropLtK a bs else b :: bs := by
  change Bool.rec (motive := fun _ => List Nat) (b :: bs) (dropLtK a bs) (Nat.blt b a) = _
  rw [bltQ]
  by_cases h : b < a <;> simp [h]

theorem dropLtK_sub (a : Nat) : ∀ bs : List Nat, (dropLtK a bs).Sublist bs
  | [] => List.Sublist.slnil
  | b :: bs => by
    rw [dropLtK_cons]
    split_ifs
    · exact (dropLtK_sub a bs).cons b
    · exact List.Sublist.refl _

theorem mem_dropLtK (a : Nat) {bs : List Nat} (hb : bs.Pairwise (· < ·)) (x : Nat) :
    x ∈ dropLtK a bs ↔ x ∈ bs ∧ a ≤ x := by
  induction bs with
  | nil => simp [dropLtK]
  | cons b bs ih =>
    rw [List.pairwise_cons] at hb
    rw [dropLtK_cons, List.mem_cons]
    split_ifs with h
    · rw [ih hb.2]
      constructor
      · exact fun h1 => ⟨Or.inr h1.1, h1.2⟩
      · rintro ⟨rfl | h1, h2⟩
        · omega
        · exact ⟨h1, h2⟩
    · rw [List.mem_cons]
      constructor
      · rintro (rfl | h1)
        · exact ⟨Or.inl rfl, by omega⟩
        · exact ⟨Or.inr h1, by have := hb.1 x h1; omega⟩
      · exact fun h1 => h1.1

theorem mergeFK_cons_nil {a : Nat} {as bs : List Nat} (h : dropLtK a bs = []) :
    mergeFK (a :: as) bs = [] := by
  change List.rec (motive := fun _ => List Nat) []
    (fun b rest _ => Bool.rec (motive := fun _ => List Nat) (mergeFK as (b :: rest))
      (a :: mergeFK as rest) (Nat.beq a b)) (dropLtK a bs) = []
  rw [h]

theorem mergeFK_cons_cons {a b : Nat} {as bs rest : List Nat} (h : dropLtK a bs = b :: rest) :
    mergeFK (a :: as) bs = if a = b then a :: mergeFK as rest else mergeFK as (b :: rest) := by
  change List.rec (motive := fun _ => List Nat) []
    (fun b rest _ => Bool.rec (motive := fun _ => List Nat) (mergeFK as (b :: rest))
      (a :: mergeFK as rest) (Nat.beq a b)) (dropLtK a bs) = _
  rw [h]
  change Bool.rec (motive := fun _ => List Nat) (mergeFK as (b :: rest)) (a :: mergeFK as rest)
    (Nat.beq a b) = _
  rw [beqQ]
  by_cases hab : a = b <;> simp [hab]

theorem mergeFK_eq : ∀ {as bs : List Nat}, as.Pairwise (· < ·) → bs.Pairwise (· < ·) →
    mergeFK as bs = as.filter fun x => decide (x ∈ bs)
  | [], _, _, _ => rfl
  | a :: as, bs, ha, hb => by
    rw [List.pairwise_cons] at ha
    have hm := mem_dropLtK a hb
    have hds : (dropLtK a bs).Pairwise (· < ·) := hb.sublist (dropLtK_sub a bs)
    have hk : ∀ x ∈ as, (x ∈ bs ↔ x ∈ dropLtK a bs) := fun x hx => by
      rw [hm]
      have := ha.1 x hx
      exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
    cases hd : dropLtK a bs with
    | nil =>
      rw [mergeFK_cons_nil hd]
      symm
      rw [List.filter_eq_nil_iff]
      intro x hx
      simp only [decide_eq_true_eq]
      intro hxb
      have hx' : x ∈ dropLtK a bs := by
        rw [hm]
        refine ⟨hxb, ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_refl _
        · exact le_of_lt (ha.1 x hx)
      rw [hd] at hx'
      simp at hx'
    | cons b rest =>
      rw [hd] at hds hk
      have hb' : b ∈ bs ∧ a ≤ b := (hm b).1 (by rw [hd]; exact List.mem_cons_self ..)
      rw [List.pairwise_cons] at hds
      rw [mergeFK_cons_cons hd, List.filter_cons]
      by_cases hab : a = b
      · subst hab
        rw [ite_eq_left rfl, ite_eq_left (by simpa using hb'.1), mergeFK_eq ha.2 hds.2]
        congr 1
        refine List.filter_congr fun x hx => ?_
        have hax := ha.1 x hx
        have hxa : x ≠ a := by omega
        simp only [hk x hx, List.mem_cons]
        simp [hxa]
      · rw [ite_eq_right hab, ite_eq_right ?_, mergeFK_eq ha.2 (List.pairwise_cons.2 hds)]
        · exact List.filter_congr fun x hx => by simp only [hk x hx]
        · simp only [decide_eq_true_eq]
          intro haB
          have h2 := (hm a).2 ⟨haB, le_refl _⟩
          rw [hd, List.mem_cons] at h2
          rcases h2 with h2 | h2
          · exact hab h2
          · have := hds.1 a h2
            omega

@[expose] noncomputable def updI (st : List Nat) (y : Nat) : List Nat :=
  mergeFK st (FixTab24.F24.getD y [])

theorem F24_eq {y : Nat} (hy : y < 191) :
    FixTab24.F24.getD y [] = (List.range (2 ^ 11)).filter fun m =>
      actM (T24.Mc.getD y []) m == m := by
  have hMc : T24.Mc.length = 192 := by rw [T24.mcOK, List.length_map, T24.pOK]; simp [T24.lenOK.1]
  rw [fixTab_get FixTab24.tab y (by rw [List.length_take, hMc]; omega)]
  simp [List.getD_eq_getElem?_getD, hy]

def RI (st : List (List Nat) × List Nat) (st' : List Nat) : Prop :=
  st.2 = st' ∧ st'.Pairwise (· < ·) ∧ ∀ x ∈ st', x < 2 ^ 11

theorem RI_upd (st : List (List Nat) × List Nat) (st' : List Nat) (y : Nat) (hy : y < 191)
    (h : RI st st') : RI (T24.Mc.getD y [] :: st.1, fixLstQ (T24.Mc.getD y []) st.2)
      (updI st' y) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hF := F24_eq hy
  have e : updI st' y = st'.filter fun m => actM (T24.Mc.getD y []) m == m := by
    rw [updI, mergeFK_eq h2 (by rw [hF]; exact List.pairwise_lt_range.filter _)]
    refine List.filter_congr fun x hx => ?_
    rw [hF]
    have hx' : x < 2048 := h3 x hx
    rw [Bool.eq_iff_iff]
    simp [List.mem_filter, List.mem_range, hx']
  refine ⟨?_, ?_, ?_⟩
  · rw [e, fixLstQ_eq, h1]
  · rw [e]
    exact h2.filter _
  · rw [e]
    exact fun x hx => h3 x (List.mem_filter.1 hx).1

@[expose] noncomputable def blk (i : Nat) : Bool :=
  gRowS 191 updI (fun L _ st => predOff24K T24.P L ([], st)) 6 [] [191] (2 ^ 191 - 1)
    (FixTab24.F24.getD i []) T24.rows 0 i

end CertificateChecks.KernelHMathieu.C490011

end

set_option maxHeartbeats 0

#kss_each CertificateChecks.KernelHMathieu.C490011.B CertificateChecks.KernelHMathieu.C490011.blk 191

public section

namespace CertificateChecks.KernelHMathieu.C490011

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

theorem search : gAllR 191 (fun st y => (T24.Mc.getD y [] :: st.1,
      fixLstQ (T24.Mc.getD y []) st.2)) (fun L _ st => predOff24K T24.P L st) 7
    [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11)) T24.rows 0 = true := by
  have hl := T24.lenOK.2
  have hMc : T24.Mc.length = 192 := by rw [T24.mcOK, List.length_map, T24.pOK]; simp [T24.lenOK.1]
  refine gAllR_succ_of_rows _ _ _ 6 _ _ _ _ _ _
    (fun i => ([T24.Mc.getD i []], FixTab24.F24.getD i [])) (by decide +kernel)
    (fun i hi => ?_) fun i hi => ?_
  swap
  · have h191 : i < 191 := by omega
    have hF := F24_eq h191
    have hR : RI ([T24.Mc.getD i []], FixTab24.F24.getD i []) (FixTab24.F24.getD i []) :=
      ⟨rfl, by rw [hF]; exact List.pairwise_lt_range.filter _,
        fun x hx => by rw [hF] at hx; exact List.mem_range.1 (List.mem_filter.1 hx).1⟩
    exact (gRowS_sim 191 (fun st y => (T24.Mc.getD y [] :: st.1,
      fixLstQ (T24.Mc.getD y []) st.2)) updI (fun L _ st => predOff24K T24.P L st)
      (fun L _ st => predOff24K T24.P L ([], st)) RI 191
      (fun l S st st' h => by
        obtain ⟨a, b⟩ := st
        cases h.1
        rfl)
      (fun st st' y hy h => RI_upd st st' y hy h) 6 [] [191] (2 ^ 191 - 1) _ _ T24.rows 0 i hR
      (by omega)).trans (B.all i h191)
  have h191 : i < 191 := by omega
  change (T24.Mc.getD (0 + i) [] :: [], fixLstQ (T24.Mc.getD (0 + i) []) (List.range (2 ^ 11))) =
    ([T24.Mc.getD i []], FixTab24.F24.getD i [])
  rw [Nat.zero_add, fixLstQ_eq, fixTab_get FixTab24.tab i (by rw [List.length_take, hMc]; omega)]
  simp [List.getD_eq_getElem?_getD, h191]

end CertificateChecks.KernelHMathieu.C490011

end
