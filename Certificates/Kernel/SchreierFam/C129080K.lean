module

public import Certificates.Kernel.SchreierFam.Co2Slp
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D1Check
public meta import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D1Check
public meta import Certificates.Kernel.SporSch.Co2M.EnumGen
public meta import CFSG.Sporadic.Co2Cert.Data
meta import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Co2M.Class
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.Co2Slp

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

meta def stageRows (st : D1Stage) : Array (Array Nat) :=
  let V := CFSG.Sporadic.Co2Cert.co2PackedVecs
  let B := CertificateChecks.KernelSporSch.Co2M.Gen.basisOf V
  let row := fun a => CertificateChecks.KernelSporSch.Co2M.Gen.rowsOf
    (CertificateChecks.KernelSporSch.Co2M.Gen.matOf V B a)
  let A := slpFinal (d1Base ()) d1SlpA
  (slpFinal (selArr A st.gens) st.slp).foldl (fun acc a =>
    (acc.push (row a)).push (row (CFSG.Monster.B.Co2.Native.invCand 2300 a))) #[]

meta def rows1 : Array (Array Nat) := stageRows d1Stage1

meta def rows2 : Array (Array Nat) := stageRows d1Stage2

meta def rows3 : Array (Array Nat) := stageRows d1Stage3

end CertificateChecks.KernelSchreierFam.Co2Slp

end

#kmisc_packarrs CertificateChecks.KernelSchreierFam.Co2Slp.SP1
  CertificateChecks.KernelSchreierFam.Co2Slp.rows1 22
#kmisc_packarrs CertificateChecks.KernelSchreierFam.Co2Slp.SP2
  CertificateChecks.KernelSchreierFam.Co2Slp.rows2 22
#kmisc_packarrs CertificateChecks.KernelSchreierFam.Co2Slp.SP3
  CertificateChecks.KernelSchreierFam.Co2Slp.rows3 22

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.Co2Slp

open CertificateChecks.KernelSporSch.Co2M CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2
  CFSG.KS.MatRep CFSG.KS.Co2M

@[expose] noncomputable def d1T : List (ℕ × ℕ) := aT ++ [zP, tP] ++ cT ++ dT

@[expose] noncomputable def d1E : List (ℕ × ℕ) := extP mmK I22 d1T d1SlpA

@[expose] noncomputable def pairsOf (P : ℕ → ℕ) (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).map fun j => (P (2 * j), P (2 * j + 1))

@[expose] noncomputable def stageK (st : D1Stage) (P : ℕ → ℕ) : Bool :=
  st.gens.all (fun i => Nat.blt (i - 1) d1E.length) &&
    treeOK (pairsOf P (st.gens.length + st.slp.length)) (selT d1E st.gens) st.slp &&
    slpT2 (pairsOf P (st.gens.length + st.slp.length)) (selT d1E st.gens)
      (selT d1E st.gens).length st.slp st.w0 st.w1

theorem d1_k : slpM d1E d1T d1T.length d1SlpA d1EqsA d1NesA = true := by decide +kernel

theorem d1_s1 : stageK d1Stage1 SP1 = true := by decide +kernel

theorem d1_s2 : stageK d1Stage2 SP2 = true := by decide +kernel

theorem d1_s3 : stageK d1Stage3 SP3 = true := by decide +kernel

theorem d1_neg : stageK { d1Stage1 with w0 := d1Stage1.w1, w1 := d1Stage1.w0 } SP1 = false ∧
    stageK d1Stage1 SP2 = false := by
  constructor <;> decide +kernel

end CertificateChecks.KernelSchreierFam.Co2Slp
