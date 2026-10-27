
module

public import CFSG.Quasithin.Recognition.CertTitsEnum4
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Kernel.SporSch.Tits.Central2263

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSporSch.TitsHelp CFSG.Certificates.Native
open CertificateChecks.KernelSporSch.TitsCentral

variable {PS PSI LR TR TRI : Nat → Nat} {kS BP : Nat} {S : Array (Array Nat)} {base : Array Nat}

theorem pg_id {i : Nat} (hi : i < 1755) : pg 11 (mask 11) (pidn 1755 11) i = i := by
  rw [← unpack_getT hi, ← CertificateChecks.KernelSporSch.TitsCentral.id_eq,
    CFSG.Monster.B.Co2.idA_get hi]

theorem prod4_gen {n w t0 t1 t2 t3 T I : Nat} {A0 A1 A2 A3 : Array Nat}
    (k0 : canonK n w (mask w) (n * w) t0 = true) (k1 : canonK n w (mask w) (n * w) t1 = true)
    (k2 : canonK n w (mask w) (n * w) t2 = true) (k3 : canonK n w (mask w) (n * w) t3 = true)
    (kT : canonK n w (mask w) (n * w) T = true) (kI : canonK n w (mask w) (n * w) I = true)
    (hI : ∀ i < n, pg w (mask w) I i = i)
    (E0 : ∀ x < n, A0[x]! = pg w (mask w) t0 x) (E1 : ∀ x < n, A1[x]! = pg w (mask w) t1 x)
    (E2 : ∀ x < n, A2[x]! = pg w (mask w) t2 x) (E3 : ∀ x < n, A3[x]! = pg w (mask w) t3 x) :
    compA n (compA n (compA n A0 A1) A2) A3 = unpack n w (prod5K n w (mask w) t0 t1 t2 t3 I) ∧
      compA n (compA n (compA n (compA n A0 A1) A2) A3) (unpack n w T) =
        unpack n w (prod5K n w (mask w) t0 t1 t2 t3 T) := by
  obtain ⟨-, hP⟩ := gpt_facts k0 k1 k2 k3 kI
  obtain ⟨-, hQ⟩ := gpt_facts k0 k1 k2 k3 kT
  obtain ⟨-, -, -, r1⟩ := canonK_facts k1
  obtain ⟨-, -, -, r2⟩ := canonK_facts k2
  obtain ⟨-, -, -, r3⟩ := canonK_facts k3
  obtain ⟨-, -, -, rT⟩ := canonK_facts kT
  have core : ∀ i < n, (compA n (compA n (compA n A0 A1) A2) A3)[i]! =
      pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 (pg w (mask w) t3 i))) := by
    intro i hi
    rw [CFSG.Monster.B.Co2.compA_get hi, E3 i hi, CFSG.Monster.B.Co2.compA_get (r3 i hi),
      E2 _ (r3 i hi), CFSG.Monster.B.Co2.compA_get (r2 _ (r3 i hi)), E1 _ (r2 _ (r3 i hi)),
      E0 _ (r1 _ (r2 _ (r3 i hi)))]
  constructor
  · apply Array.ext
    · simp [compA, unpack]
    · intro i h1 _
      have hi : i < n := by simpa [compA] using h1
      rw [← getElem!_pos _ i h1, ← getElem!_pos _ i (by simpa [unpack] using hi), (hP i hi).1, core i hi]
      unfold gpt
      rw [hI i hi]
  · apply Array.ext
    · simp [compA, unpack]
    · intro i h1 _
      have hi : i < n := by simpa [compA] using h1
      rw [← getElem!_pos _ i h1, ← getElem!_pos _ i (by simpa [unpack] using hi), (hQ i hi).1,
        CFSG.Monster.B.Co2.compA_get hi, unpack_getT hi, core _ (rT i hi)]
      rfl

theorem prod4_eq {t0 t1 t2 t3 T : Nat} {A0 A1 A2 A3 : Array Nat}
    (k0 : C t0) (k1 : C t1) (k2 : C t2) (k3 : C t3) (kT : C T)
    (E0 : ∀ x < 1755, A0[x]! = pg 11 (mask 11) t0 x) (E1 : ∀ x < 1755, A1[x]! = pg 11 (mask 11) t1 x)
    (E2 : ∀ x < 1755, A2[x]! = pg 11 (mask 11) t2 x) (E3 : ∀ x < 1755, A3[x]! = pg 11 (mask 11) t3 x) :
    compA 1755 (compA 1755 (compA 1755 A0 A1) A2) A3 =
        unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 (pidn 1755 11)) ∧
      compA 1755 (compA 1755 (compA 1755 (compA 1755 A0 A1) A2) A3) (unpack 1755 11 T) =
        unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 T) :=
  prod4_gen k0 k1 k2 k3 kT canId (fun _ hi => pg_id hi) E0 E1 E2 E3

theorem table4_size (hb : Binds 1755 11 PS kS 4 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 4 BP) :
    (CFSG.Quasithin.table4 1755 (rawLevels 1755 S base)).size =
      rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) * rcnt (LR 3) := by
  rw [CFSG.Quasithin.table4, (lev_trAt hb hp hl (i := 0) (by omega)).1,
    (lev_trAt hb hp hl (i := 1) (by omega)).1, (lev_trAt hb hp hl (i := 2) (by omega)).1,
    (lev_trAt hb hp hl (i := 3) (by omega)).1]
  simp [List.length_flatMap, List.sum_replicate, Nat.mul_assoc]

theorem table4_all (hb : Binds 1755 11 PS kS 4 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 4 BP) {T : Nat} (kT : C T) {f : Array Nat → Bool}
    (h : ∀ a < rcnt (LR 0), ∀ b < rcnt (LR 1), ∀ c < rcnt (LR 2), ∀ d < rcnt (LR 3),
      C (trAt 1755 (1755 * 11) LR TR 0 a) → C (trAt 1755 (1755 * 11) LR TR 1 b) →
      C (trAt 1755 (1755 * 11) LR TR 2 c) → C (trAt 1755 (1755 * 11) LR TR 3 d) →
      f (unpack 1755 11 (prod5K 1755 11 (mask 11) (trAt 1755 (1755 * 11) LR TR 0 a)
        (trAt 1755 (1755 * 11) LR TR 1 b) (trAt 1755 (1755 * 11) LR TR 2 c)
        (trAt 1755 (1755 * 11) LR TR 3 d) (pidn 1755 11))) = true ∧
      f (unpack 1755 11 (prod5K 1755 11 (mask 11) (trAt 1755 (1755 * 11) LR TR 0 a)
        (trAt 1755 (1755 * 11) LR TR 1 b) (trAt 1755 (1755 * 11) LR TR 2 c)
        (trAt 1755 (1755 * 11) LR TR 3 d) T)) = true) :
    ∀ y ∈ (CFSG.Quasithin.table4 1755 (rawLevels 1755 S base)).toList,
      f y = true ∧ f (compA 1755 y (unpack 1755 11 T)) = true := by
  have L0 := lev_trAt hb hp hl (i := 0) (by omega)
  have L1 := lev_trAt hb hp hl (i := 1) (by omega)
  have L2 := lev_trAt hb hp hl (i := 2) (by omega)
  have L3 := lev_trAt hb hp hl (i := 3) (by omega)
  intro y hy
  rw [CFSG.Quasithin.table4, List.toList_toArray, L0.1, L1.1, L2.1, L3.1] at hy
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hy
  obtain ⟨a, ha, b, hb', c, hc, d, hd, rfl⟩ := hy
  obtain ⟨k0, E0, -⟩ := L0.2 a ha
  obtain ⟨k1, E1, -⟩ := L1.2 b hb'
  obtain ⟨k2, E2, -⟩ := L2.2 c hc
  obtain ⟨k3, E3, -⟩ := L3.2 d hd
  obtain ⟨e1, e2⟩ := prod4_eq k0 k1 k2 k3 kT E0 E1 E2 E3
  rw [e2, e1]
  exact h a ha b hb' c hc d hd k0 k1 k2 k3

end CertificateChecks.KernelEvenBN

end
