module

public import Certificates.Kernel.Pk442010.Grp
public import Certificates.Kernel.A45Cls.Cls
public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.OmegaPk

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPk442010

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.Pk442010
  CFSG.Certificates.Kernel.PkCV

theorem pins : (Nat.beq (cOf (Certificates.P43Twin.tA ())).1 tAL &&
    Nat.beq (cOf (Certificates.P43Twin.tB ())).1 tBL &&
    Nat.beq (cOf (Certificates.OmegaPk.g0 ())).1 g0L &&
    Nat.beq (cOf (Certificates.P43Twin.a1 ())).1 a1L &&
    Nat.beq (cOf (Certificates.P43Twin.x2 ())⁻¹).1 x2iL &&
    allN 8 (fun j => Nat.beq (cOf ((Certificates.P43Twin.Q1 ()).getD j 1)).1 (rQ1 j)) &&
    allN 8 (fun j => Nat.beq (cOf ((Certificates.P43Twin.Q2 ()).getD j 1)).1 (rQ2 j))) = true := by
  decide +kernel

theorem words : bindWs 45 6 2 KernelA45.KA.G CP.G cW 0 = true ∧
    bindWs 45 6 2 KernelA45.KA.G CQ.G cbW 0 = true ∧
    bindWs 45 6 2 rG (fun j => rR (csAt csW j)) wsR 0 = true := by
  decide +kernel

theorem ids : CP.T 0 = pidn 45 6 ∧ CQ.T 0 = pidn 45 6 := by decide +kernel

theorem rho : homK csW rR = true ∧ injK csW rR = true ∧ memRK CP.N CP.T CP.S csW rR = true ∧
    hitK csW rR tAL = true ∧ isInvK 45 6 tAL = true ∧ isInvK 45 6 tBL = true := by
  decide +kernel

theorem subQ : subK CP.N CP.T CP.S rQ1 tAL = true ∧ subK CP.N CP.T CP.S rQ2 tAL = true := by
  decide +kernel

theorem cent : centK CP.N CP.T csW rR rQ2 = true ∧ centK CP.N CP.T csW rB rQ1 = true ∧
    conjK csW rR rB g0L = true := by
  decide +kernel

theorem comm : commK csW rR rB = true ∧ memP CP.N CP.T CP.S g0L = true ∧
    prodK rQ1 rQ2 prodP = true := by
  decide +kernel

end CertificateChecks.KernelPk442010

end
