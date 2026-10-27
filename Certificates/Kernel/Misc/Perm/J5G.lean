module

public import Certificates.Kernel.Misc.Perm.J5F
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelMisc.CertBind (Bound cert_facts)
open CFSG.KC.Misc.Clos (allN_iff allR forall_of_chunks)

theorem hQGA : ∀ k < j2FiveQGenArrs.size, j2FiveQGenArrs[k]! = unpack 315 9 (QG k) := by
  intro k hk
  have hs : j2FiveQGenArrs.size = 2 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hCG0 : ∀ k < (j2FiveCG 0).size, (j2FiveCG 0)[k]! = unpack 315 9 (CGP0 k) := by
  intro k hk
  have hs : (j2FiveCG 0).size = 2 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hCG1 : ∀ k < (j2FiveCG 1).size, (j2FiveCG 1)[k]! = unpack 315 9 (CGP1 k) := by
  intro k hk
  have hs : (j2FiveCG 1).size = 2 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hCG2 : ∀ k < (j2FiveCG 2).size, (j2FiveCG 2)[k]! = unpack 315 9 (CGP2 k) := by
  intro k hk
  have hs : (j2FiveCG 2).size = 3 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hCG3 : ∀ k < (j2FiveCG 3).size, (j2FiveCG 3)[k]! = unpack 315 9 (CGP3 k) := by
  intro k hk
  have hs : (j2FiveCG 3).size = 2 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hCG4 : ∀ k < (j2FiveCG 4).size, (j2FiveCG 4)[k]! = unpack 315 9 (CGP4 k) := by
  intro k hk
  have hs : (j2FiveCG 4).size = 3 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hCG5 : ∀ k < (j2FiveCG 5).size, (j2FiveCG 5)[k]! = unpack 315 9 (CGP5 k) := by
  intro k hk
  have hs : (j2FiveCG 5).size = 3 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hDG2 : ∀ k < (j2FiveDG 2).size, (j2FiveDG 2)[k]! = unpack 315 9 (DGP2 k) := by
  intro k hk
  have hs : (j2FiveDG 2).size = 3 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hDG3 : ∀ k < (j2FiveDG 3).size, (j2FiveDG 3)[k]! = unpack 315 9 (DGP3 k) := by
  intro k hk
  have hs : (j2FiveDG 3).size = 2 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hDG5 : ∀ k < (j2FiveDG 5).size, (j2FiveDG 5)[k]! = unpack 315 9 (DGP5 k) := by
  intro k hk
  have hs : (j2FiveDG 5).size = 2 := by decide
  rw [hs] at hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem bQ : Bound 315 9 j2FiveQCert 25 2 QP.F QE.F QR.F QL.F := by
  change Bound 315 9 j2FiveQLit 25 2 QP.F QE.F QR.F QL.F
  unfold j2FiveQLit
  exact cert_facts QP.eq QP.all QE.eq QE.all QR.eq QR.all QL.eq QL.all

theorem pQ : ∀ i < 25, permB 315 9 (QP.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bC0 : Bound 315 9 (j2FiveCCert 0) 50 2 C0P.F C0E.F C0R.F C0L.F := by
  change Bound 315 9 j2FiveCLit0 50 2 C0P.F C0E.F C0R.F C0L.F
  unfold j2FiveCLit0
  exact cert_facts C0P.eq C0P.all C0E.eq C0E.all C0R.eq C0R.all C0L.eq C0L.all

theorem pC0 : ∀ i < 50, permB 315 9 (C0P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bC1 : Bound 315 9 (j2FiveCCert 1) 50 2 C1P.F C1E.F C1R.F C1L.F := by
  change Bound 315 9 j2FiveCLit1 50 2 C1P.F C1E.F C1R.F C1L.F
  unfold j2FiveCLit1
  exact cert_facts C1P.eq C1P.all C1E.eq C1E.all C1R.eq C1R.all C1L.eq C1L.all

theorem pC1 : ∀ i < 50, permB 315 9 (C1P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bC2 : Bound 315 9 (j2FiveCCert 2) 300 3 C2P.F C2E.F C2R.F C2L.F := by
  change Bound 315 9 j2FiveCLit2 300 3 C2P.F C2E.F C2R.F C2L.F
  unfold j2FiveCLit2
  exact cert_facts C2P.eq C2P.all C2E.eq C2E.all C2R.eq C2R.all C2L.eq C2L.all

theorem pC2 : ∀ i < 300, permB 315 9 (C2P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bC3 : Bound 315 9 (j2FiveCCert 3) 300 2 C3P.F C3E.F C3R.F C3L.F := by
  change Bound 315 9 j2FiveCLit3 300 2 C3P.F C3E.F C3R.F C3L.F
  unfold j2FiveCLit3
  exact cert_facts C3P.eq C3P.all C3E.eq C3E.all C3R.eq C3R.all C3L.eq C3L.all

theorem pC3 : ∀ i < 300, permB 315 9 (C3P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bC4 : Bound 315 9 (j2FiveCCert 4) 50 3 C4P.F C4E.F C4R.F C4L.F := by
  change Bound 315 9 j2FiveCLit4 50 3 C4P.F C4E.F C4R.F C4L.F
  unfold j2FiveCLit4
  exact cert_facts C4P.eq C4P.all C4E.eq C4E.all C4R.eq C4R.all C4L.eq C4L.all

theorem pC4 : ∀ i < 50, permB 315 9 (C4P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bC5 : Bound 315 9 (j2FiveCCert 5) 300 3 C5P.F C5E.F C5R.F C5L.F := by
  change Bound 315 9 j2FiveCLit5 300 3 C5P.F C5E.F C5R.F C5L.F
  unfold j2FiveCLit5
  exact cert_facts C5P.eq C5P.all C5E.eq C5E.all C5R.eq C5R.all C5L.eq C5L.all

theorem pC5 : ∀ i < 300, permB 315 9 (C5P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bD2 : Bound 315 9 (j2FiveDCert 2) 60 3 D2P.F D2E.F D2R.F D2L.F := by
  change Bound 315 9 j2FiveDLit2 60 3 D2P.F D2E.F D2R.F D2L.F
  unfold j2FiveDLit2
  exact cert_facts D2P.eq D2P.all D2E.eq D2E.all D2R.eq D2R.all D2L.eq D2L.all

theorem pD2 : ∀ i < 60, permB 315 9 (D2P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bD3 : Bound 315 9 (j2FiveDCert 3) 60 2 D3P.F D3E.F D3R.F D3L.F := by
  change Bound 315 9 j2FiveDLit3 60 2 D3P.F D3E.F D3R.F D3L.F
  unfold j2FiveDLit3
  exact cert_facts D3P.eq D3P.all D3E.eq D3E.all D3R.eq D3R.all D3L.eq D3L.all

theorem pD3 : ∀ i < 60, permB 315 9 (D3P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

theorem bD5 : Bound 315 9 (j2FiveDCert 5) 60 2 D5P.F D5E.F D5R.F D5L.F := by
  change Bound 315 9 j2FiveDLit5 60 2 D5P.F D5E.F D5R.F D5L.F
  unfold j2FiveDLit5
  exact cert_facts D5P.eq D5P.all D5E.eq D5E.all D5R.eq D5R.all D5L.eq D5L.all

theorem pD5 : ∀ i < 60, permB 315 9 (D5P.F i) = true :=
  (allN_iff _ _).1 (by quickRfl)

end CertificateChecks.KernelMisc.J2F

end
