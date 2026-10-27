module

public import Certificates.Kernel.SporSch.Ru.Tree2247

public section

namespace CertificateChecks.KernelSporSch.RuTree

open CFSG.KC.Misc.HexFlat CFSG.KS.RuTree CFSG.Sporadic.RuSchreier

@[expose] noncomputable def plK (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat)
            (entK2 16 3692 RuTreeC5.F RuTreeC5.R.F (Nat.sub c 534698))
            (entK 151 RuTreeC4.F (Nat.sub c 401365)) (Nat.blt c 534698))
          (entK 151 RuTreeC3.F (Nat.sub c 268032)) (Nat.blt c 401365))
        (entK 151 RuTreeC2.F (Nat.sub c 134699)) (Nat.blt c 268032))
      (entK 151 RuTreeC1.F (Nat.sub c 1366)) (Nat.blt c 134699))
    (entK 91 RuTreeC0.F (Nat.sub c 1)) (Nat.blt c 1366)

theorem bytes_eq : ruBytesTree = (String.ofList (RuTreeC0.chars ++ RuTreeC1.chars ++
    RuTreeC2.chars ++ RuTreeC3.chars ++ RuTreeC4.chars ++ RuTreeC5.chars)).toUTF8 := by
  rw [ruBytesTree, ruTreeText, RuTreeC0.eq, RuTreeC1.eq, RuTreeC2.eq, RuTreeC3.eq, RuTreeC4.eq,
    RuTreeC5.eq]
  simp only [String.ofList_append]

theorem rec_at {pre cs post : List Char} {K : Nat} {E : Nat → Nat}
    (hb : ruBytesTree = (String.ofList (pre ++ cs ++ post)).toUTF8) (hc : Chunk cs K E)
    (hpre : ∀ k < pre.length, AH pre[k]!) (hpost : ∀ k < post.length, AH post[k]!)
    {a c : Nat} (ha : pre.length = 6 * a) (h1 : a + 1 ≤ c) (h2 : c < a + 1 + K) :
    ruTreeParent c = E (c - (a + 1)) / 16 ∧ ruTreeGen c = E (c - (a + 1)) % 16 := by
  have e : 6 * (c - 1) = pre.length + 6 * (c - (a + 1)) := by omega
  obtain ⟨A, B⟩ := chunk_rec (pre := pre) (post := post) hc.1 hc.2.1 hc.2.2 hpre hpost
    (k := c - (a + 1)) (by omega)
  rw [ruTreeParent, ruTreeGen, ruHexAt, ruHexAt, hb, e]
  exact ⟨A, B⟩

theorem bnat' (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem pl_spec {c : Nat} (h1 : 1 ≤ c) (h2 : c < 593775) :
    ruTreeParent c = plK c / 16 ∧ ruTreeGen c = plK c % 16 := by
  have hb := bytes_eq
  have l0 := ch0.1
  have l1 := ch1.1
  have l2 := ch2.1
  have l3 := ch3.1
  have l4 := ch4.1
  have a0 := ch0.2.1
  have a1 := ch1.2.1
  have a2 := ch2.2.1
  have a3 := ch3.2.1
  have a4 := ch4.2.1
  have a5 := ch5.2.1
  unfold plK
  simp only [bnat']
  by_cases c1 : c < 1366
  · simp only [Nat.blt_eq.mpr c1, ↓reduceIte]
    refine rec_at (pre := []) (post := RuTreeC1.chars ++ RuTreeC2.chars ++ RuTreeC3.chars ++
      RuTreeC4.chars ++ RuTreeC5.chars) (a := 0) ?_ ch0
      (fun k hk => absurd hk (Nat.not_lt_zero k))
      (ah_app (ah_app (ah_app (ah_app a1 a2) a3) a4) a5) rfl (by omega) (by omega)
    rw [hb]
    simp only [List.nil_append, List.append_assoc]
  have c1' : Nat.blt c 1366 = false := by
    cases h : Nat.blt c 1366
    · rfl
    · exact absurd (Nat.blt_eq.mp h) c1
  simp only [c1', Bool.false_eq_true, ↓reduceIte]
  by_cases c2 : c < 134699
  · simp only [Nat.blt_eq.mpr c2, ↓reduceIte]
    refine rec_at (pre := RuTreeC0.chars) (post := RuTreeC2.chars ++ RuTreeC3.chars ++
      RuTreeC4.chars ++ RuTreeC5.chars) (a := 1365) ?_ ch1
      a0 (ah_app (ah_app (ah_app a2 a3) a4) a5) l0 (by omega) (by omega)
    rw [hb]
    simp only [List.append_assoc]
  have c2' : Nat.blt c 134699 = false := by
    cases h : Nat.blt c 134699
    · rfl
    · exact absurd (Nat.blt_eq.mp h) c2
  simp only [c2', Bool.false_eq_true, ↓reduceIte]
  by_cases c3 : c < 268032
  · simp only [Nat.blt_eq.mpr c3, ↓reduceIte]
    refine rec_at (pre := RuTreeC0.chars ++ RuTreeC1.chars) (post := RuTreeC3.chars ++
      RuTreeC4.chars ++ RuTreeC5.chars) (a := 134698) ?_ ch2
      (ah_app a0 a1) (ah_app (ah_app a3 a4) a5)
      (by rw [List.length_append, l0, l1]) (by omega) (by omega)
    rw [hb]
    simp only [List.append_assoc]
  have c3' : Nat.blt c 268032 = false := by
    cases h : Nat.blt c 268032
    · rfl
    · exact absurd (Nat.blt_eq.mp h) c3
  simp only [c3', Bool.false_eq_true, ↓reduceIte]
  by_cases c4 : c < 401365
  · simp only [Nat.blt_eq.mpr c4, ↓reduceIte]
    refine rec_at (pre := RuTreeC0.chars ++ RuTreeC1.chars ++ RuTreeC2.chars)
      (post := RuTreeC4.chars ++ RuTreeC5.chars) (a := 268031) ?_ ch3
      (ah_app (ah_app a0 a1) a2) (ah_app a4 a5)
      (by rw [List.length_append, List.length_append, l0, l1, l2]) (by omega) (by omega)
    rw [hb]
    simp only [List.append_assoc]
  have c4' : Nat.blt c 401365 = false := by
    cases h : Nat.blt c 401365
    · rfl
    · exact absurd (Nat.blt_eq.mp h) c4
  simp only [c4', Bool.false_eq_true, ↓reduceIte]
  by_cases c5 : c < 534698
  · simp only [Nat.blt_eq.mpr c5, ↓reduceIte]
    refine rec_at (pre := RuTreeC0.chars ++ RuTreeC1.chars ++ RuTreeC2.chars ++ RuTreeC3.chars)
      (post := RuTreeC5.chars) (a := 401364) ?_ ch4
      (ah_app (ah_app (ah_app a0 a1) a2) a3) a5
      (by rw [List.length_append, List.length_append, List.length_append, l0, l1, l2, l3])
      (by omega) (by omega)
    exact hb
  have c5' : Nat.blt c 534698 = false := by
    cases h : Nat.blt c 534698
    · rfl
    · exact absurd (Nat.blt_eq.mp h) c5
  simp only [c5', Bool.false_eq_true, ↓reduceIte]
  refine rec_at (pre := RuTreeC0.chars ++ RuTreeC1.chars ++ RuTreeC2.chars ++ RuTreeC3.chars ++
    RuTreeC4.chars) (post := []) (a := 534697) ?_ ch5
    (ah_app (ah_app (ah_app (ah_app a0 a1) a2) a3) a4)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
    (by rw [List.length_append, List.length_append, List.length_append, List.length_append, l0,
      l1, l2, l3, l4]) (by omega) (by omega)
  rw [hb]
  simp only [List.append_nil]

end CertificateChecks.KernelSporSch.RuTree

end
