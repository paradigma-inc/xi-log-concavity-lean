import ProofWorkspace.Final.SourcePanel47CheckpointsFull
import ProofWorkspace.Final.SourceCoefficientSlice00Full
import ProofWorkspace.Final.SourceCoefficientSlice01Full
import ProofWorkspace.Final.SourceCoefficientSlice02Full
import ProofWorkspace.Final.SourceCoefficientSlice03Full
import ProofWorkspace.Final.SourceCoefficientSlice04Full
import ProofWorkspace.Final.SourceCoefficientSlice05Full
import ProofWorkspace.Final.SourceCoefficientSlice06Full
import ProofWorkspace.Final.SourceCoefficientSlice07Full
import ProofWorkspace.Final.SourceCoefficientSlice08Full
import ProofWorkspace.Final.SourceCoefficientSlice09Full
import ProofWorkspace.Final.SourceCoefficientSlice10Full
import ProofWorkspace.Final.SourceCoefficientSlice11Full
import ProofWorkspace.Final.SourceCoefficientSlice12Full
import ProofWorkspace.Final.SourceCoefficientSlice13Full
import ProofWorkspace.Final.SourceCoefficientSlice14Full
import ProofWorkspace.Final.SourceCoefficientSlice15Full
import ProofWorkspace.Final.SourceCoefficientSlice16Full
import ProofWorkspace.Final.SourceCoefficientSlice17Full
import ProofWorkspace.Final.SourceCoefficientSlice18Full
import ProofWorkspace.Final.SourceCoefficientSlice19Full
import ProofWorkspace.Final.SourceCoefficientSlice20Full
import ProofWorkspace.Final.SourceCoefficientSlice21Full
import ProofWorkspace.Final.SourceCoefficientSlice22Full
import ProofWorkspace.Final.SourceCoefficientSlice23Full
import ProofWorkspace.Final.SourceCoefficientSlice24Full
import ProofWorkspace.Final.SourceCoefficientSlice25Full
import ProofWorkspace.Final.SourceCoefficientSlice26Full
import ProofWorkspace.Final.SourceCoefficientSlice27Full
import ProofWorkspace.Final.SourceCoefficientSlice28Full
import ProofWorkspace.Final.SourceCoefficientSlice29Full
import ProofWorkspace.Final.SourceCoefficientSlice30Full
import ProofWorkspace.Final.SourceCoefficientSlice31Full
import ProofWorkspace.Final.SourceCoefficientSlice32Full
import ProofWorkspace.Final.SourceCoefficientSlice33Full
import ProofWorkspace.Final.SourceCoefficientSlice34Full
import ProofWorkspace.Final.SourceCoefficientSlice35Full
import ProofWorkspace.Final.SourceCoefficientSlice36Full
import ProofWorkspace.Final.SourceCoefficientSlice37Full
import ProofWorkspace.Final.SourceCoefficientSlice38Full
import ProofWorkspace.Final.SourceCoefficientSlice39Full
import ProofWorkspace.Final.SourceCoefficientSlice40Full
import ProofWorkspace.Final.SourceCoefficientSlice41Full
import ProofWorkspace.Final.SourceCoefficientSlice42Full
import ProofWorkspace.Final.SourceCoefficientSlice43Full
import ProofWorkspace.Final.SourceCoefficientSlice44Full
import ProofWorkspace.Final.SourceCoefficientSlice45Full
import ProofWorkspace.Final.SourceCoefficientSlice46Full
import ProofWorkspace.Final.SourceCoefficientSlice47Full
import ProofWorkspace.Final.SourceCoefficientSlice48Full
import ProofWorkspace.Final.SourceCoefficientSlice49Full
import ProofWorkspace.Final.SourceCoefficientSlice50Full
import ProofWorkspace.Final.SourceCoefficientSlice51Full
import ProofWorkspace.Final.SourceCoefficientSlice52Full
import ProofWorkspace.Final.SourceCoefficientSlice53Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel47Seed_checked :
    intSourceTrigSeed (ratSourcePanelCenter ⟨47, by decide⟩/40) = sourcePanel47Seed := by
  have hc : ratSourcePanelCenter ⟨47, by decide⟩/40 = (95/8000:ℚ) := by
    norm_num [ratSourcePanelCenter]
  rw [hc]
  decide +kernel

theorem sourcePanel47Checkpoint_zero :
    sourcePanel47Checkpoint 0 = (((sourceCoefficientScale:ℤ),0),List.replicate 65 0) := by
  decide +kernel

theorem sourcePanel47Chunk00_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 0 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 0
    sourceCoefficientSlice00 sourceCoefficientSlice00_checked
  decide +kernel

theorem sourcePanel47Chunk01_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 1 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 1
    sourceCoefficientSlice01 sourceCoefficientSlice01_checked
  decide +kernel

theorem sourcePanel47Chunk02_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 2 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 2
    sourceCoefficientSlice02 sourceCoefficientSlice02_checked
  decide +kernel

theorem sourcePanel47Chunk03_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 3 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 3
    sourceCoefficientSlice03 sourceCoefficientSlice03_checked
  decide +kernel

theorem sourcePanel47Chunk04_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 4 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 4
    sourceCoefficientSlice04 sourceCoefficientSlice04_checked
  decide +kernel

theorem sourcePanel47Chunk05_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 5 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 5
    sourceCoefficientSlice05 sourceCoefficientSlice05_checked
  decide +kernel

theorem sourcePanel47Chunk06_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 6 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 6
    sourceCoefficientSlice06 sourceCoefficientSlice06_checked
  decide +kernel

theorem sourcePanel47Chunk07_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 7 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 7
    sourceCoefficientSlice07 sourceCoefficientSlice07_checked
  decide +kernel

theorem sourcePanel47Chunk08_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 8 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 8
    sourceCoefficientSlice08 sourceCoefficientSlice08_checked
  decide +kernel

theorem sourcePanel47Chunk09_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 9 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 9
    sourceCoefficientSlice09 sourceCoefficientSlice09_checked
  decide +kernel

theorem sourcePanel47Chunk10_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 10 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 10
    sourceCoefficientSlice10 sourceCoefficientSlice10_checked
  decide +kernel

theorem sourcePanel47Chunk11_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 11 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 11
    sourceCoefficientSlice11 sourceCoefficientSlice11_checked
  decide +kernel

theorem sourcePanel47Chunk12_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 12 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 12
    sourceCoefficientSlice12 sourceCoefficientSlice12_checked
  decide +kernel

theorem sourcePanel47Chunk13_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 13 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 13
    sourceCoefficientSlice13 sourceCoefficientSlice13_checked
  decide +kernel

theorem sourcePanel47Chunk14_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 14 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 14
    sourceCoefficientSlice14 sourceCoefficientSlice14_checked
  decide +kernel

theorem sourcePanel47Chunk15_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 15 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 15
    sourceCoefficientSlice15 sourceCoefficientSlice15_checked
  decide +kernel

theorem sourcePanel47Chunk16_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 16 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 16
    sourceCoefficientSlice16 sourceCoefficientSlice16_checked
  decide +kernel

theorem sourcePanel47Chunk17_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 17 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 17
    sourceCoefficientSlice17 sourceCoefficientSlice17_checked
  decide +kernel

theorem sourcePanel47Chunk18_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 18 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 18
    sourceCoefficientSlice18 sourceCoefficientSlice18_checked
  decide +kernel

theorem sourcePanel47Chunk19_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 19 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 19
    sourceCoefficientSlice19 sourceCoefficientSlice19_checked
  decide +kernel

theorem sourcePanel47Chunk20_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 20 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 20
    sourceCoefficientSlice20 sourceCoefficientSlice20_checked
  decide +kernel

theorem sourcePanel47Chunk21_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 21 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 21
    sourceCoefficientSlice21 sourceCoefficientSlice21_checked
  decide +kernel

theorem sourcePanel47Chunk22_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 22 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 22
    sourceCoefficientSlice22 sourceCoefficientSlice22_checked
  decide +kernel

theorem sourcePanel47Chunk23_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 23 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 23
    sourceCoefficientSlice23 sourceCoefficientSlice23_checked
  decide +kernel

theorem sourcePanel47Chunk24_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 24 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 24
    sourceCoefficientSlice24 sourceCoefficientSlice24_checked
  decide +kernel

theorem sourcePanel47Chunk25_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 25 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 25
    sourceCoefficientSlice25 sourceCoefficientSlice25_checked
  decide +kernel

theorem sourcePanel47Chunk26_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 26 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 26
    sourceCoefficientSlice26 sourceCoefficientSlice26_checked
  decide +kernel

theorem sourcePanel47Chunk27_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 27 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 27
    sourceCoefficientSlice27 sourceCoefficientSlice27_checked
  decide +kernel

theorem sourcePanel47Chunk28_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 28 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 28
    sourceCoefficientSlice28 sourceCoefficientSlice28_checked
  decide +kernel

theorem sourcePanel47Chunk29_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 29 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 29
    sourceCoefficientSlice29 sourceCoefficientSlice29_checked
  decide +kernel

theorem sourcePanel47Chunk30_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 30 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 30
    sourceCoefficientSlice30 sourceCoefficientSlice30_checked
  decide +kernel

theorem sourcePanel47Chunk31_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 31 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 31
    sourceCoefficientSlice31 sourceCoefficientSlice31_checked
  decide +kernel

theorem sourcePanel47Chunk32_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 32 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 32
    sourceCoefficientSlice32 sourceCoefficientSlice32_checked
  decide +kernel

theorem sourcePanel47Chunk33_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 33 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 33
    sourceCoefficientSlice33 sourceCoefficientSlice33_checked
  decide +kernel

theorem sourcePanel47Chunk34_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 34 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 34
    sourceCoefficientSlice34 sourceCoefficientSlice34_checked
  decide +kernel

theorem sourcePanel47Chunk35_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 35 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 35
    sourceCoefficientSlice35 sourceCoefficientSlice35_checked
  decide +kernel

theorem sourcePanel47Chunk36_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 36 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 36
    sourceCoefficientSlice36 sourceCoefficientSlice36_checked
  decide +kernel

theorem sourcePanel47Chunk37_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 37 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 37
    sourceCoefficientSlice37 sourceCoefficientSlice37_checked
  decide +kernel

theorem sourcePanel47Chunk38_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 38 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 38
    sourceCoefficientSlice38 sourceCoefficientSlice38_checked
  decide +kernel

theorem sourcePanel47Chunk39_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 39 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 39
    sourceCoefficientSlice39 sourceCoefficientSlice39_checked
  decide +kernel

theorem sourcePanel47Chunk40_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 40 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 40
    sourceCoefficientSlice40 sourceCoefficientSlice40_checked
  decide +kernel

theorem sourcePanel47Chunk41_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 41 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 41
    sourceCoefficientSlice41 sourceCoefficientSlice41_checked
  decide +kernel

theorem sourcePanel47Chunk42_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 42 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 42
    sourceCoefficientSlice42 sourceCoefficientSlice42_checked
  decide +kernel

theorem sourcePanel47Chunk43_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 43 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 43
    sourceCoefficientSlice43 sourceCoefficientSlice43_checked
  decide +kernel

theorem sourcePanel47Chunk44_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 44 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 44
    sourceCoefficientSlice44 sourceCoefficientSlice44_checked
  decide +kernel

theorem sourcePanel47Chunk45_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 45 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 45
    sourceCoefficientSlice45 sourceCoefficientSlice45_checked
  decide +kernel

theorem sourcePanel47Chunk46_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 46 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 46
    sourceCoefficientSlice46 sourceCoefficientSlice46_checked
  decide +kernel

theorem sourcePanel47Chunk47_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 47 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 47
    sourceCoefficientSlice47 sourceCoefficientSlice47_checked
  decide +kernel

theorem sourcePanel47Chunk48_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 48 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 48
    sourceCoefficientSlice48 sourceCoefficientSlice48_checked
  decide +kernel

theorem sourcePanel47Chunk49_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 49 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 49
    sourceCoefficientSlice49 sourceCoefficientSlice49_checked
  decide +kernel

theorem sourcePanel47Chunk50_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 50 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 50
    sourceCoefficientSlice50 sourceCoefficientSlice50_checked
  decide +kernel

theorem sourcePanel47Chunk51_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 51 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 51
    sourceCoefficientSlice51 sourceCoefficientSlice51_checked
  decide +kernel

theorem sourcePanel47Chunk52_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 52 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 52
    sourceCoefficientSlice52 sourceCoefficientSlice52_checked
  decide +kernel

theorem sourcePanel47Chunk53_checked :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint 53 := by
  apply sourcePanelChunkCheck_of_slice sourcePanel47Seed sourcePanel47Checkpoint 53
    sourceCoefficientSlice53 sourceCoefficientSlice53_checked
  decide +kernel

theorem sourcePanel47Chunks_checked (i : Fin 54) :
    sourcePanelChunkCheck sourcePanel47Seed sourcePanel47Checkpoint i := by
  fin_cases i
  · exact sourcePanel47Chunk00_checked
  · exact sourcePanel47Chunk01_checked
  · exact sourcePanel47Chunk02_checked
  · exact sourcePanel47Chunk03_checked
  · exact sourcePanel47Chunk04_checked
  · exact sourcePanel47Chunk05_checked
  · exact sourcePanel47Chunk06_checked
  · exact sourcePanel47Chunk07_checked
  · exact sourcePanel47Chunk08_checked
  · exact sourcePanel47Chunk09_checked
  · exact sourcePanel47Chunk10_checked
  · exact sourcePanel47Chunk11_checked
  · exact sourcePanel47Chunk12_checked
  · exact sourcePanel47Chunk13_checked
  · exact sourcePanel47Chunk14_checked
  · exact sourcePanel47Chunk15_checked
  · exact sourcePanel47Chunk16_checked
  · exact sourcePanel47Chunk17_checked
  · exact sourcePanel47Chunk18_checked
  · exact sourcePanel47Chunk19_checked
  · exact sourcePanel47Chunk20_checked
  · exact sourcePanel47Chunk21_checked
  · exact sourcePanel47Chunk22_checked
  · exact sourcePanel47Chunk23_checked
  · exact sourcePanel47Chunk24_checked
  · exact sourcePanel47Chunk25_checked
  · exact sourcePanel47Chunk26_checked
  · exact sourcePanel47Chunk27_checked
  · exact sourcePanel47Chunk28_checked
  · exact sourcePanel47Chunk29_checked
  · exact sourcePanel47Chunk30_checked
  · exact sourcePanel47Chunk31_checked
  · exact sourcePanel47Chunk32_checked
  · exact sourcePanel47Chunk33_checked
  · exact sourcePanel47Chunk34_checked
  · exact sourcePanel47Chunk35_checked
  · exact sourcePanel47Chunk36_checked
  · exact sourcePanel47Chunk37_checked
  · exact sourcePanel47Chunk38_checked
  · exact sourcePanel47Chunk39_checked
  · exact sourcePanel47Chunk40_checked
  · exact sourcePanel47Chunk41_checked
  · exact sourcePanel47Chunk42_checked
  · exact sourcePanel47Chunk43_checked
  · exact sourcePanel47Chunk44_checked
  · exact sourcePanel47Chunk45_checked
  · exact sourcePanel47Chunk46_checked
  · exact sourcePanel47Chunk47_checked
  · exact sourcePanel47Chunk48_checked
  · exact sourcePanel47Chunk49_checked
  · exact sourcePanel47Chunk50_checked
  · exact sourcePanel47Chunk51_checked
  · exact sourcePanel47Chunk52_checked
  · exact sourcePanel47Chunk53_checked

end ReciprocalXi
