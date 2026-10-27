module

public import Certificates.Kernel.PermCent.U43P1Tab
public import Certificates.Data.Kernel.PermCent.U43P1Chk
public import Certificates.Data.Kernel.PermCent.U43P1W
public import Certificates.Kernel.PermCent.U43P1A6

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def memCM1a (v : ℕ) : Bool :=
  (List.range 720).any fun j => Nat.beq (CgM1a.T j) v

@[expose] noncomputable def memCIa (v : ℕ) : Bool :=
  (List.range 720).any fun j => Nat.beq (CgIa.T j) v

@[expose] noncomputable def cfgM1aK (k : ℕ) : Bool :=
  commOK (pk (wM1a.getD k (0, false)).1 (wM1a.getD k (0, false)).2) (clsT 1 (clsR 1)) &&
    ((List.range (tM1a.getD k []).length).all fun j => commOK (tM1aG k j) (clsT 1 (clsR 1))) &&
    Nat.beq (cfgM1a.getD k []).length (cond (Nat.beq k 0) 16 32) &&
    cfgOK (tM1aT k) a6T a6N (!Nat.beq k 0) memCM1a (invL.map LM1a.T) (pk cDi false)
      (pk cDmi false) (cfgM1a.getD k [])

@[expose] noncomputable def cfgIaK (k : ℕ) : Bool :=
  commOK (pk (wIa.getD k (0, false)).1 (wIa.getD k (0, false)).2) (clsT 5 (clsR 5)) &&
    ((List.range (tIa.getD k []).length).all fun j => commOK (tIaG k j) (clsT 5 (clsR 5))) &&
    Nat.beq (cfgIa.getD k []).length (cond (Nat.beq k 0) 16 32) &&
    cfgOK (tIaT k) a6T a6N (!Nat.beq k 0) memCIa (invL.map LIa.T) (pk cDi false)
      (pk cDmi false) (cfgIa.getD k [])

@[expose] noncomputable def noneIa (u : ℕ) : Bool :=
  isId (pc u u) &&
    !(List.range 4536).any fun j => Nat.beq (CIa.T j) (pc u (pc (clsT 5 (clsR 5)) u))

theorem cfgM1a_lo : (cfgM1aK 0 && cfgM1aK 1 && cfgM1aK 2) = true := by decide +kernel

theorem cfgM1a_hi : (cfgM1aK 3 && cfgM1aK 4 && cfgM1aK 5) = true := by decide +kernel

theorem cfgIa_all : (cfgIaK 0 && cfgIaK 1 && cfgIaK 2 && cfgIaK 3 && noneIa (pk cI true) &&
    noneIa (pk cM1 true)) = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43P1

end
