module

public import Certificates.Data.Fi24Rank.PlanesCheck
import Certificates.Kernel.LocalComp.Fi24Pl.Checks
import Certificates.Kernel.LocalComp.Fi24TwoB.F15027
import CFSG.Certificates.Kernel.Fi24Pl.Sound
import CFSG.Certificates.Kernel.Spor.HexNumsSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import Certificates.Kernel.Sporadic.ON.Gen

#kon_join CertificateChecks.KernelLC.Fi24PlK.iotaAll CertificateChecks.KernelLC.Fi24PlK.iotaC 16
#kon_join CertificateChecks.KernelLC.Fi24PlK.rowAll CertificateChecks.KernelLC.Fi24PlK.row 64

namespace CertificateChecks.KernelLC.Fi24PlA

open CFSG.KC.Enum CFSG.KC.Fi24Pl CFSG.KC.Fi24PlS CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.LocalAnalysis.GLTheoremA.H301B.Fi24PlanesNative
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.RankThree.Native (enumOK_spec permsA rep_of_validA keyA validA)
open CertificateChecks.KernelLC

theorem pg_unpack {n p x : Nat} (hx : x < n) : pg 9 511 p x = (unpack n 9 p)[x]! := by
  rw [CFSG.KS.Raw.Orb.unpack_get hx]
  rfl

theorem rowsOf_get {a : Array Nat} (hs : a.size = 2520) {k x : Nat} (hk : k < 5) (hx : x < 504) :
    ((rowsOf 504 a)[k]!)[x]! = a[504 * k + x]! := by
  have hsz : (rowsOf 504 a).size = 5 := by
    unfold rowsOf
    rw [Array.size_ofFn, hs]
  have e1 : (rowsOf 504 a)[k]! = a.extract (k * 504) (k * 504 + 504) := by
    rw [getElem!_pos (rowsOf 504 a) k (by rw [hsz]; exact hk)]
    unfold rowsOf
    rw [Array.getElem_ofFn]
  have hle : k * 504 + 504 ≤ a.size := by
    rw [hs]
    omega
  have h2 : x < (a.extract (k * 504) (k * 504 + 504)).size := by
    rw [Array.size_extract, Nat.min_eq_left hle, Nat.add_sub_cancel_left]
    exact hx
  have h3 : k * 504 + x < a.size := by
    rw [hs]
    omega
  rw [e1, getElem!_pos _ x h2, Array.getElem_extract, Nat.mul_comm 504 k, getElem!_pos a _ h3]

theorem kra_get : ∀ k < 5, ∀ x < 504, ((kRA ())[k]!)[x]! = aK Fi24PlT.A.F k x := by
  intro k hk x hx
  have ha : hexNums 3 kRAText = unpack 2520 9 Fi24PlT.A.F :=
    CFSG.KS.HexNums.hexNums_of Fi24PlT.A.eq Fi24PlT.A.ok
  have hs : (unpack 2520 9 Fi24PlT.A.F).size = 2520 := Array.size_ofFn
  unfold kRA
  rw [ha, rowsOf_get hs hk hx]
  unfold aK
  rw [pg_unpack (n := 2520) (by change 504 * k + x < 2520; omega)]
  rfl

theorem iota_all : ∀ i < 243, iotaK Fi24PlT.A.F Fi24PlD.IK i = true := by
  intro i hi
  have hc : i / 16 < 16 := by omega
  have h := allN_spec (Fi24PlK.iotaAll (i / 16) hc) (i % 16) (Nat.mod_lt _ (by decide))
  rw [CFSG.KC.Fi24PlS.strictB_eq] at h
  have e : Nat.add (Nat.mul 16 (i / 16)) (i % 16) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e, (Nat.blt_eq.mpr hi : Nat.blt i 243 = true)] at h
  exact h

theorem row_all : ∀ t < 4096, rowK Fi24PlD.IK Fi24PlD.V Fi24BN.T Fi24PlD.BT t = true := by
  intro t ht
  have hc : t / 64 < 64 := by omega
  have h0 := Fi24PlK.rowAll (t / 64) hc
  unfold Fi24PlK.row rowC at h0
  have h := allN_spec h0 (t % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 64 (t / 64)) (t % 64) = t := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  change rowK Fi24PlD.IK Fi24PlD.V Fi24BN.T Fi24PlD.BT (Nat.add (Nat.mul 64 (t / 64)) (t % 64)) =
    true at h
  rw [e] at h
  exact h

theorem pt_lt {t x : Nat} (ht : t < 4096) (hx : x < 504) :
    (fi24NCert.pts[t]!)[x]! = pg 9 511 (Fi24BN.T t) x := by
  rw [Fi24B.pt_get ht, pg_unpack hx]

theorem spec : (∀ x, x ∈ fi24N ↔ ∃ i < fi24NCert.pts.size, permOfArr 504 fi24NCert.pts[i]! = x) ∧
    Nat.card fi24N = fi24NCert.pts.size ∧
    ∀ i < fi24NCert.pts.size, validA 504 fi24NCert.pts[i]! = true :=
  enumOK_spec fi24NKey_lt Fi24B.enum_ok

theorem valid {t : Nat} (ht : t < 4096) : validA 504 fi24NCert.pts[t]! = true :=
  spec.2.2 t (by rw [Fi24B.pts_size]; exact ht)

theorem tp {t : Nat} (ht : t < 4096) (x : Fin 504) :
    pg 9 511 (Fi24BN.T t) x = (permOfArr 504 fi24NCert.pts[t]! x : Nat) := by
  rw [← pt_lt ht x.2]
  exact (rep_of_validA (valid ht)).apply x.2

theorem gp {j : Nat} (hj : j < 12) (x : Fin 504) :
    pg 9 511 (Fi24BN.G j) x = (permOfArr 504 fi24NGens[j]! x : Nat) := by
  have hv := CFSG.RankThree.Native.enumOK_gens_valid Fi24B.enum_ok
    (by rw [fi24NGens_size]; exact hj)
  rw [pg_unpack x.2, ← Fi24B.gens_get hj]
  exact (rep_of_validA hv).apply x.2

theorem keys {a : Nat} (ha : a < 4096) {b : Nat} (hb : b < 4096)
    (h : ∀ r < 6, pg 9 511 (Fi24BN.T a) (bp r) = pg 9 511 (Fi24BN.T b) (bp r)) : a = b := by
  refine Fi24B.ptKeys a (by rw [Fi24B.pts_size]; exact ha) b (by rw [Fi24B.pts_size]; exact hb) ?_
  have e : ∀ r < 6, (fi24NCert.pts[a]!)[bp r]! = (fi24NCert.pts[b]!)[bp r]! := fun r hr => by
    rw [pt_lt ha (bp_lt hr), pt_lt hb (bp_lt hr)]
    exact h r hr
  have e0 : (fi24NCert.pts[a]!)[4]! = (fi24NCert.pts[b]!)[4]! := e 0 (by decide)
  have e1 : (fi24NCert.pts[a]!)[0]! = (fi24NCert.pts[b]!)[0]! := e 1 (by decide)
  have e2 : (fi24NCert.pts[a]!)[1]! = (fi24NCert.pts[b]!)[1]! := e 2 (by decide)
  have e3 : (fi24NCert.pts[a]!)[2]! = (fi24NCert.pts[b]!)[2]! := e 3 (by decide)
  have e4 : (fi24NCert.pts[a]!)[3]! = (fi24NCert.pts[b]!)[3]! := e 4 (by decide)
  have e5 : (fi24NCert.pts[a]!)[6]! = (fi24NCert.pts[b]!)[6]! := e 5 (by decide)
  unfold keyA fi24NKey
  simp only [List.map_cons, List.map_nil]
  rw [e0, e1, e2, e3, e4, e5]

theorem t0 : ∀ x < 504, pg 9 511 (Fi24BN.T 0) x = x := by
  intro x hx
  have k := Fi24BN.kHead
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, _⟩ := k
  rw [Nat.eq_of_beq_eq_true h3, pg_unpack hx, ← Fi24B.idA_eq, idA_get hx]

end CertificateChecks.KernelLC.Fi24PlA

public section

namespace CertificateChecks.KernelLC.Fi24PlA

open CFSG.KC.Fi24PlS CFSG.LocalAnalysis.GLTheoremA.H301B.Fi24PlanesNative
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CFSG.Monster.B.Co2

theorem planes : fi24PlanesOK () = true := by
  unfold fi24PlanesOK
  exact planesCheck_of (N := fi24N) (Tp := fun t => permOfArr 504 fi24NCert.pts[t]!)
    (Gp := fun j => permOfArr 504 fi24NGens[j]!) kra_get Fi24PlK.basis iota_all Fi24PlK.inv
    Fi24PlK.norm row_all Fi24PlK.final Fi24B.pts_size (fun t ht x hx => pt_lt ht hx)
    (fun t ht x => tp ht x)
    (fun t ht => (spec.1 _).2 ⟨t, by rw [Fi24B.pts_size]; exact ht, rfl⟩)
    (fun y hy => by
      obtain ⟨t, ht, e⟩ := (spec.1 y).1 hy
      exact ⟨t, by rw [← Fi24B.pts_size]; exact ht, e⟩)
    (fun j hj x => gp hj x)
    (by
      rw [fi24N]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, by rw [← fi24NGens_size]; exact hk, rfl⟩)
    (fun a ha b hb h => keys ha hb h) t0

end CertificateChecks.KernelLC.Fi24PlA

end
