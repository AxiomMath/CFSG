module

public import Certificates.Kernel.L34Syl.Data

public section

namespace CertificateChecks.KernelL34Syl

open CFSG.KC.L34Syl

theorem ch465003_rec5a : recsK 42 6 63 252 pm252 5 9 896 PT RT5 K5A REC5A 0 = true := by
  decide +kernel

theorem ch465003_rec5b : recsK 42 6 63 252 pm252 5 9 896 PT RT5 K5B REC5B K5A = true := by
  decide +kernel

theorem ch465003_rec5c : recsK 42 6 63 252 pm252 5 9 896 PT RT5 K5C REC5C K5B = true := by
  decide +kernel

theorem ch465003_rec5d : recsK 42 6 63 252 pm252 5 9 896 PT RT5 K5D REC5D K5C = true := by
  decide +kernel

theorem ch465003_rec7a : recsK 42 6 63 252 pm252 7 9 672 PT RT7 K7A REC7A 0 = true := by
  decide +kernel

theorem ch465003_rec7b : recsK 42 6 63 252 pm252 7 9 672 PT RT7 K7B REC7B K7A = true := by
  decide +kernel

end CertificateChecks.KernelL34Syl

end
