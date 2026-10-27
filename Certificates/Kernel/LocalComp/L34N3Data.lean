module

public import Certificates.Kernel.LocalComp.L34N3Gen
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelLC.L34N3.KRP include_bytes "data/L34N3.KRP.items" 15 16502442370366853680

#kc_items CertificateChecks.KernelLC.L34N3.T0 include_bytes "data/L34N3.T0.items" 61440 9678955082773325943
#kc_items CertificateChecks.KernelLC.L34N3.E0 include_bytes "data/L34N3.E0.items" 17760 11864628100026941536
#kc_items CertificateChecks.KernelLC.L34N3.S0 include_bytes "data/L34N3.S0.items" 4735 13001584990637635498
#kc_items CertificateChecks.KernelLC.L34N3.SI0 include_bytes "data/L34N3.SI0.items" 4736 15620897142341909364
#kc_items CertificateChecks.KernelLC.L34N3.T1 include_bytes "data/L34N3.T1.items" 71680 15296533175407585354
#kc_items CertificateChecks.KernelLC.L34N3.E1 include_bytes "data/L34N3.E1.items" 20720 9011228739160744104
#kc_items CertificateChecks.KernelLC.L34N3.S1 include_bytes "data/L34N3.S1.items" 5530 7234357527744808824
#kc_items CertificateChecks.KernelLC.L34N3.SI1 include_bytes "data/L34N3.SI1.items" 5533 4222275738655429063
#kc_items CertificateChecks.KernelLC.L34N3.T2 include_bytes "data/L34N3.T2.items" 21504 13444733050608695966
#kc_items CertificateChecks.KernelLC.L34N3.E2 include_bytes "data/L34N3.E2.items" 6215 15807377101441784673
#kc_items CertificateChecks.KernelLC.L34N3.S2 include_bytes "data/L34N3.S2.items" 1638 10357606689782715390
#kc_items CertificateChecks.KernelLC.L34N3.SI2 include_bytes "data/L34N3.SI2.items" 1638 7053059527163955906

#kc_items CertificateChecks.KernelLC.L34N3.X0 include_bytes "data/L34N3.X0.items" 124 16647055834878954737
#kc_items CertificateChecks.KernelLC.L34N3.P0 include_bytes "data/L34N3.P0.items" 756 2339594723935649345
#kc_items CertificateChecks.KernelLC.L34N3.X1 include_bytes "data/L34N3.X1.items" 50 9506977180478117223
#kc_items CertificateChecks.KernelLC.L34N3.P1 include_bytes "data/L34N3.P1.items" 324 15410428239768474380
#kc_items CertificateChecks.KernelLC.L34N3.X2 include_bytes "data/L34N3.X2.items" 355 4421966893227067402
#kc_items CertificateChecks.KernelLC.L34N3.P2 include_bytes "data/L34N3.P2.items" 2160 5016336108701920283

namespace CertificateChecks.KernelLC.L34N3

open CertificateChecks.KernelLC.L34X

@[expose] noncomputable def KR (c : Nat) : Nat := KRP c

@[expose] noncomputable def ON (c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 1920, nIf(Nat.beq c (nat_lit 1), nat_lit 2240, nat_lit 672))

@[expose] noncomputable def CN (c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 21, nIf(Nat.beq c (nat_lit 1), nat_lit 9, nat_lit 60))

@[expose] noncomputable def OT (c j : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), at8 T0 (nat_lit 252) j,
    nIf(Nat.beq c (nat_lit 1), at8 T1 (nat_lit 252) j, at8 T2 (nat_lit 252) j))

@[expose] noncomputable def OE (c j : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), at16 E0 (nat_lit 72) j,
    nIf(Nat.beq c (nat_lit 1), at16 E1 (nat_lit 72) j, at16 E2 (nat_lit 72) j))

@[expose] noncomputable def OS (c j : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), at16 S0 (nat_lit 18) j,
    nIf(Nat.beq c (nat_lit 1), at16 S1 (nat_lit 18) j, at16 S2 (nat_lit 18) j))

@[expose] noncomputable def OSI (c j : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), at16 SI0 (nat_lit 18) j,
    nIf(Nat.beq c (nat_lit 1), at16 SI1 (nat_lit 18) j, at16 SI2 (nat_lit 18) j))

@[expose] noncomputable def CX (c k : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), X0 k, nIf(Nat.beq c (nat_lit 1), X1 k, X2 k))

@[expose] noncomputable def CP (c k : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), P0 k, nIf(Nat.beq c (nat_lit 1), P1 k, P2 k))

end CertificateChecks.KernelLC.L34N3

end
