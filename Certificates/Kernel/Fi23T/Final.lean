module

public import Certificates.Kernel.Fi23T.Local

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23T

open CFSG.Sporadic.Fi23.Native (WOrbit TrComp trCompute trChecks trCertificate trData cData PBits pOf
  trIncOK trMemOK trStarOK trGensOK trCommOK trDomOK trCsOK trOrbitOK trRowOK trFarOK trMuOK trEdOK
  starPts starPhiPos trLetters trD trBi trPhi dTable genTables pZero)
open CFSG.Sporadic.Th.Native (Table)
open CFSG.KD.Fi23K (orbLit orbitData_eq')

theorem trChecks_of {O : WOrbit} {D bi : Table} {z : PBits} {C : TrComp} {chunks : ℕ}
    (h1 : trIncOK (cData ()) 1080 = true) (h2 : trIncOK (trData ()) 3240 = true)
    (h3 : trMemOK (pOf z (cData ())) (cData ()) = true)
    (h4 : trMemOK (pOf z (trData ())) (trData ()) = true)
    (h5 : trStarOK O D bi (starPts D) (starPhiPos ()) (pOf z (cData ())) = true)
    (h6 : trGensOK (pOf z (cData ())) (pOf z (trData ())) (trLetters O D bi) C.treeC C.treeR = true)
    (h7 : trCommOK O D bi (pOf z (cData ())) C.cord C.cpar = true)
    (h8 : trDomOK O D bi (pOf z (cData ())) (pOf z (trData ())) C.domW C.ncW = true)
    (h9 : trCsOK O D bi (pOf z (cData ())) (pOf z (trData ())) = true)
    (h10 : trOrbitOK O.alpha O.beta z (pOf z (trData ())) C.orb chunks = true)
    (h11 : trRowOK O C.orb (trD C.orb) (trBi C.orb) (pOf z (trData ())) C.rowInv = true)
    (h12 : trFarOK O C.orb (trD C.orb) (trBi C.orb) (pOf z (trData ())) C.rowInv
      (trPhi O C.orb (trD C.orb) (trBi C.orb)) C.v0 C.farTree = true)
    (h13 : trMuOK O C.orb (trD C.orb) (trBi C.orb) C.rowInv C.v0 C.mOrd C.mPar C.mWit C.mH
      C.muPos = true)
    (h14 : trEdOK O C.orb (trD C.orb) (trBi C.orb) C.rowInv C.v0 C.mOrd C.edX C.edK = true) :
    trChecks O D bi z C chunks = true := by
  unfold trChecks
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.and_self]

noncomputable abbrev TC : TrComp := trCompute orbLit (dTable orbLit) (genTables orbLit (-2)) (pZero ())

theorem tc_treeC : TC.treeC = CFSG.Perm.Native.treeBFS 31671 0
    (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))
    (Array.range CFSG.Sporadic.Fi23.Native.cGens.size) := by unfold TC trCompute; rfl
theorem tc_treeR : TC.treeR = CFSG.Perm.Native.treeBFS 31671 (CFSG.Sporadic.Fi23.Native.rRoot ())
    (trLetters orbLit (dTable orbLit) (genTables orbLit (-2)))
    (Array.range CFSG.Sporadic.Fi23.Native.cGens.size) := by unfold TC trCompute; rfl
theorem tc_cord : TC.cord = CT.1 := by unfold TC trCompute; rfl
theorem tc_cpar : TC.cpar = CT.2 := by unfold TC trCompute; rfl
set_option simprocs false in
theorem tc_domW : TC.domW = DW := by
  unfold TC trCompute DW
  dsimp only
set_option simprocs false in
theorem tc_ncW : TC.ncW = NW := by
  unfold TC trCompute NW
  dsimp only
theorem tc_orb : TC.orb = orb := by unfold TC trCompute; rfl
theorem tc_rowInv : TC.rowInv = RI := by unfold TC trCompute; rfl
set_option simprocs false in
theorem tc_v0 : TC.v0 = V0 := by
  unfold TC trCompute V0
  dsimp only
theorem tc_farTree : TC.farTree = FT := by unfold TC trCompute; rfl
theorem tc_mOrd : TC.mOrd = MT.1 := by unfold TC trCompute; rfl
theorem tc_mPar : TC.mPar = MT.2.1 := by unfold TC trCompute; rfl
theorem tc_mWit : TC.mWit = MT.2.2.1 := by unfold TC trCompute; rfl
theorem tc_mH : TC.mH = MT.2.2.2.1 := by unfold TC trCompute; rfl
theorem tc_muPos : TC.muPos = CFSG.KS.Fi23Tr.muPosOf MT.1 := by unfold TC trCompute; rfl
theorem tc_edX : TC.edX = ED.1 := by unfold TC trCompute; rfl
theorem tc_edK : TC.edK = ED.2 := by unfold TC trCompute; rfl


theorem tr_ok : trCertificate 3 = true := by
  unfold trCertificate
  rw [orbitData_eq']
  refine trChecks_of (O := orbLit) (D := dTable orbLit) (bi := genTables orbLit (-2))
    (z := pZero ()) (C := TC) (chunks := 3) inc_c inc_t mem_c mem_t star_ok' ?_ ?_ ?_ cs_ok' ?_ ?_ ?_
    ?_ ?_
  · rw [tc_treeC, tc_treeR]
    exact gens_ok'
  · rw [tc_cord, tc_cpar]
    exact comm_ok
  · rw [tc_domW, tc_ncW]
    exact dom_ok'
  · rw [tc_orb]
    exact orbit_ok
  · rw [tc_orb, tc_rowInv]
    exact row_ok
  · rw [tc_orb, tc_rowInv, tc_v0, tc_farTree]
    exact far_ok
  · rw [tc_orb, tc_rowInv, tc_v0, tc_mOrd, tc_mPar, tc_mWit, tc_mH, tc_muPos]
    exact mu_ok
  · rw [tc_orb, tc_rowInv, tc_v0, tc_mOrd, tc_edX, tc_edK]
    exact ed_ok

end CertificateChecks.KernelFi23T

end
