import ProofWorkspace.Final.SourcePanelCompositionFull

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
namespace ReciprocalXi

abbrev SourcePanelCheckpointState := (ℤ × ℤ) × List ℤ

def sourcePanelChunkCheck (seed : ℤ × ℤ) (checkpoint : ℕ → SourcePanelCheckpointState)
    (i : ℕ) : Prop :=
  let k := 256*i
  let n := min 256 (13601-k)
  let s := checkpoint i
  (((intSourceTrigStep seed)^[n]) s.1,
    intSourceCoefficientValuesFrom sourcePiMidpoint seed 65 k
      ((sourceMidpointArray.toList.drop k).take n) s.1 s.2) = checkpoint (i+1)

instance sourcePanelChunkCheck_decidable (seed : ℤ × ℤ)
    (checkpoint : ℕ → SourcePanelCheckpointState) (i : ℕ) :
    Decidable (sourcePanelChunkCheck seed checkpoint i) := by
  unfold sourcePanelChunkCheck
  infer_instance

def sourcePanelRemaining (seed : ℤ × ℤ) (checkpoint : ℕ → SourcePanelCheckpointState)
    (i : ℕ) : List ℤ :=
  intSourceCoefficientValuesFrom sourcePiMidpoint seed 65
    (min (256*i) 13601) (sourceMidpointArray.toList.drop (min (256*i) 13601))
    (checkpoint i).1 (checkpoint i).2

theorem sourcePanelRemaining_step (seed : ℤ × ℤ)
    (checkpoint : ℕ → SourcePanelCheckpointState) (i : ℕ) (hi : i<54)
    (hc : sourcePanelChunkCheck seed checkpoint i) :
    sourcePanelRemaining seed checkpoint i=sourcePanelRemaining seed checkpoint (i+1) := by
  have hk : min (256*i) 13601=256*i := Nat.min_eq_left (by omega)
  have hs : 256*i+min 256 (13601-256*i)=min (256*(i+1)) 13601 := by omega
  have harray : sourceMidpointArray.toList.length=13601 := sourceMidpointArray_size
  have hlen : ((sourceMidpointArray.toList.drop (256*i)).take
      (min 256 (13601-256*i))).length=min 256 (13601-256*i) := by
    rw [List.length_take,List.length_drop,harray]
    exact Nat.min_eq_left (by omega)
  have hdrop : (sourceMidpointArray.toList.drop (256*i)).drop
      (min 256 (13601-256*i))=sourceMidpointArray.toList.drop (min (256*(i+1)) 13601) := by
    rw [List.drop_drop]
    congr 1
  unfold sourcePanelChunkCheck at hc
  have ht := congrArg Prod.fst hc
  have ha := congrArg Prod.snd hc
  dsimp only at ht ha
  unfold sourcePanelRemaining
  rw [hk,←List.take_append_drop (min 256 (13601-256*i))
    (sourceMidpointArray.toList.drop (256*i))]
  rw [intSourceCoefficientValuesFrom_append,hlen,hdrop,hs,ht,ha]

theorem sourcePanelRemaining_all (seed : ℤ × ℤ)
    (checkpoint : ℕ → SourcePanelCheckpointState)
    (hc : ∀ i : Fin 54, sourcePanelChunkCheck seed checkpoint i)
    (i : ℕ) (hi : i≤54) :
    sourcePanelRemaining seed checkpoint 0=sourcePanelRemaining seed checkpoint i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    exact (ih (by omega)).trans
      (sourcePanelRemaining_step seed checkpoint i (by omega) (hc ⟨i,by omega⟩))

theorem sourcePanelRemaining_final (seed : ℤ × ℤ)
    (checkpoint : ℕ → SourcePanelCheckpointState) :
    sourcePanelRemaining seed checkpoint 54=(checkpoint 54).2 := by
  have hdrop : sourceMidpointArray.toList.drop 13601=[] :=
    List.drop_eq_nil_of_le (le_of_eq sourceMidpointArray_size)
  unfold sourcePanelRemaining
  rw [show min (256*54) 13601=13601 from by decide,hdrop]
  rfl

theorem sourcePanelValues_eq_checkpoint (c : ℚ) (seed : ℤ × ℤ)
    (checkpoint : ℕ → SourcePanelCheckpointState)
    (hseed : intSourceTrigSeed (c/40)=seed)
    (hzero : checkpoint 0=(((sourceCoefficientScale:ℤ),0),List.replicate 65 0))
    (hc : ∀ i : Fin 54, sourcePanelChunkCheck seed checkpoint i) :
    intSourceCoefficientValues c sourcePiMidpoint sourceMidpointArray.toList=
      (checkpoint 54).2 := by
  have hstart : intSourceCoefficientValues c sourcePiMidpoint sourceMidpointArray.toList=
      sourcePanelRemaining seed checkpoint 0 := by
    unfold intSourceCoefficientValues sourcePanelRemaining
    rw [hseed,hzero]
    simp only [Nat.mul_zero,Nat.zero_min,List.drop_zero]
  exact hstart.trans ((sourcePanelRemaining_all seed checkpoint hc 54 (by omega)).trans
    (sourcePanelRemaining_final seed checkpoint))

theorem sourcePanelStream_eq_checkpoint (j : Fin 318) (seed : ℤ × ℤ)
    (checkpoint : ℕ → SourcePanelCheckpointState)
    (hseed : intSourceTrigSeed (ratSourcePanelCenter j/40)=seed)
    (hzero : checkpoint 0=(((sourceCoefficientScale:ℤ),0),List.replicate 65 0))
    (hc : ∀ i : Fin 54, sourcePanelChunkCheck seed checkpoint i) :
    intSourceCoefficientStream (ratSourcePanelCenter j) sourcePiMidpoint sourceRoundedMidpoint=
      (checkpoint 54).2 := by
  exact (intSourceCoefficientValues_array_eq_stream (ratSourcePanelCenter j)
    sourcePiMidpoint sourceMidpointArray sourceMidpointArray_size).symm.trans
    (sourcePanelValues_eq_checkpoint _ seed checkpoint hseed hzero hc)

end ReciprocalXi
