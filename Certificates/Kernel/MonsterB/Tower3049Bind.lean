module

public import Certificates.Kernel.MonsterB.Tower3049Data
public import CFSG.Certificates.Kernel.MonsterB.TowerSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import Mathlib.Tactic.Ring.RingNF

public section

namespace CertificateChecks.Tower3049

open CFSG.Monster.B.Max2.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Tower

theorem unpack_get {n w X i : Nat} (hi : i < n) : (unpack n w X)[i]! = pg w (mask w) X i := by
  rw [unpack, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem hexTable_get {d n k₀ i : Nat} {s : String} (hi : i < n) :
    (CFSG.Monster.B.Co2.Native.hexTable d n k₀ s)[i]! =
      CFSG.Monster.B.Co2.Native.hexAt s.toUTF8 (d * (k₀ + i)) d := by
  rw [CFSG.Monster.B.Co2.Native.hexTable, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem dag_field {j i : Nat} (hj : j < 5282) (hi : i < 2) :
    CFSG.Monster.B.Co2.Native.hexAt dagHex.toUTF8 (4 * (2 * j + i)) 4 =
      pg 16 (mask 16) (Certificates.Tw3049D.F j) i := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Certificates.Tw3049D.all j hj
  rw [← Certificates.Tw3049D.eq] at h
  have e := congrArg (fun A : Array Nat => A[i]!) h
  simp only at e
  rw [hexTable_get hi, unpack_get hi] at e
  exact e

theorem dag_get : ∀ j < 5282, (towerDag ())[j]! = ((DA j : Int) - 4, DB j) := by
  intro j hj
  rw [getElem!_pos _ _ (by rw [towerDag_size]; exact hj)]
  simp only [towerDag, Array.getElem_ofFn]
  rw [hexAt_eq, hexAt_eq]
  have e0 := dag_field hj (i := 0) (by omega)
  have e1 := dag_field hj (i := 1) (by omega)
  rw [show 4 * (2 * j + 0) = 8 * j by omega] at e0
  rw [show 4 * (2 * j + 1) = 8 * j + 4 by omega] at e1
  rw [e0, e1]
  rfl

theorem pt_byte {k i : Nat} (hk : k < 4802) (hi : i < 5) :
    CFSG.Monster.B.Co2.Native.hexAt pointsHex.toUTF8 (10 * k + 2 * i) 2 = PB k i := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Certificates.Tw3049P.all k hk
  rw [← Certificates.Tw3049P.eq] at h
  have e := congrArg (fun A : Array Nat => A[i]!) h
  simp only at e
  rw [hexTable_get hi, unpack_get hi, show 2 * (5 * k + i) = 10 * k + 2 * i by omega] at e
  exact e

theorem towerPointsAll_size : (towerPointsAll ()).size = 4802 := by
  unfold towerPointsAll
  rw [Array.size_ofFn]
  rfl

theorem pts_get : ∀ k < 4802, (towerPointsAll ())[k]! = (V k, W k) := by
  intro k hk
  have hs := towerPointsAll_size
  rw [getElem!_pos _ _ (by rw [hs]; exact hk)]
  simp only [towerPointsAll, Array.getElem_ofFn]
  rw [hexAt_eq, hexAt_eq]
  have b : ∀ i < 5, CFSG.Monster.B.Co2.Native.hexAt pointsHex.toUTF8 (10 * k + 2 * i) 2 = PB k i :=
    fun i hi => pt_byte hk hi
  have v : CFSG.Monster.B.Co2.Native.hexAt pointsHex.toUTF8 (10 * k) 6 = V k := by
    rw [show (6 : Nat) = 2 + 4 from rfl, hexAt_add, show (4 : Nat) = 2 + 2 from rfl, hexAt_add]
    have b0 := b 0 (by omega)
    have b1 := b 1 (by omega)
    have b2 := b 2 (by omega)
    rw [show 10 * k + 2 * 0 = 10 * k by omega] at b0
    rw [show 10 * k + 2 * 1 = 10 * k + 2 by omega] at b1
    rw [show 10 * k + 2 * 2 = 10 * k + 2 + 2 by omega] at b2
    rw [b0, b1, b2, V]
    ring
  have w : CFSG.Monster.B.Co2.Native.hexAt pointsHex.toUTF8 (10 * k + 6) 4 = W k := by
    rw [show (4 : Nat) = 2 + 2 from rfl, hexAt_add]
    have b3 := b 3 (by omega)
    have b4 := b 4 (by omega)
    rw [show 10 * k + 2 * 3 = 10 * k + 6 by omega] at b3
    rw [show 10 * k + 2 * 4 = 10 * k + 6 + 2 by omega] at b4
    rw [b3, b4, W]
    ring
  rw [v, w]

end CertificateChecks.Tower3049

end
