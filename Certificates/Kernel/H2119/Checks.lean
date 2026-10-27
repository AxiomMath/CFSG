module

public import Certificates.Data.Kernel.Hering2119K
public import Certificates.Kernel.H2119.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KD.H2119

open CFSG.KC.H2119

theorem ch522001_n1 : nOK (lineK 1) N1 = true := by quickRfl

theorem ch522001_n2 : nOK (lineK 2) N2 = true := by quickRfl

theorem ch522001_n3 : nOK (lineK 3) N3 = true := by quickRfl

theorem ch522001_l1 : chkL N1 L1 = true := by quickRfl

theorem ch522001_l2 : chkL N2 L2 = true := by quickRfl

theorem ch522001_l3 : chkL N3 L3 = true := by quickRfl

theorem ch522001_c : conjsOK Rep0 Rep1 C = true := by quickRfl

theorem ch522001_w01 : rowsK Rep0.1 Rep0.2 (lineK 1) S01 L1 W01 = true := by quickRfl

theorem ch522001_w02 : rowsK Rep0.1 Rep0.2 (lineK 2) S02 L2 W02 = true := by quickRfl

theorem ch522001_w03 : rowsK Rep0.1 Rep0.2 (lineK 3) S03 L3 W03 = true := by quickRfl

theorem ch522001_w11 : rowsK Rep1.1 Rep1.2 (lineK 1) S11 L1 W11 = true := by quickRfl

theorem ch522001_w12 : rowsK Rep1.1 Rep1.2 (lineK 2) S12 L2 W12 = true := by quickRfl

theorem ch522001_w13 : rowsK Rep1.1 Rep1.2 (lineK 3) S13 L3 W13 = true := by quickRfl

theorem ch522001_k0 : conclAll Rep0.1 S01 S02 S03 = true := by quickRfl

theorem ch522001_k1 : conclAll Rep1.1 S11 S12 S13 = true := by quickRfl

end CertificateChecks.KD.H2119
