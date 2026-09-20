import Submissions.UpperCompressions.Reconstruct

/-! Width-generic codec for a nonce followed by a disclosure payload. No scheme or
security claim is made here. Short bit strings decode with zero extension; exact
re-encoding is asserted only when the nonce is fully present. -/

namespace OptimalOTS.WeightedConstruction.NonceCodec

abbrev Signature (n : ℕ) := BitVec n × List Bool

def encode {n : ℕ} (σ : Signature n) : List Bool := toBits σ.1 ++ σ.2

def decode (n : ℕ) (bits : List Bool) : Signature n :=
  (ofBits n (bits.take n), bits.drop n)

@[simp] theorem length_encode {n : ℕ} (σ : Signature n) :
    (encode σ).length = n + σ.2.length := by
  simp [encode, toBits]

@[simp] theorem decode_encode {n : ℕ} (σ : Signature n) : decode n (encode σ) = σ := by
  rcases σ with ⟨nonce, payload⟩
  have hn : (toBits nonce).length = n := length_toBits nonce
  simp only [decode, encode, List.take_left' hn, List.drop_left' hn, ofBits_toBits]

theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro a b h
  have := congrArg (decode n) h
  simpa using this

theorem encode_decode {n : ℕ} (bits : List Bool) (hlen : n ≤ bits.length) :
    encode (decode n bits) = bits := by
  change toBits (ofBits n (bits.take n)) ++ bits.drop n = bits
  rw [toBits_ofBits _ (by simp [hlen]), List.take_append_drop]

@[simp] theorem length_payload_decode (n : ℕ) (bits : List Bool) :
    (decode n bits).2.length = bits.length - n := by
  simp [decode]

theorem enough_nonce_of_payload_positive {n : ℕ} {bits : List Bool}
    (h : 0 < (decode n bits).2.length) : n ≤ bits.length := by
  rw [length_payload_decode] at h
  omega

theorem canonical_of_payload_positive {n : ℕ} {bits : List Bool}
    (h : 0 < (decode n bits).2.length) : encode (decode n bits) = bits :=
  encode_decode bits (enough_nonce_of_payload_positive h)

abbrev Signature86 := Signature 86

theorem signature86_length (nonce : BitVec 86) (payload : List Bool)
    (h : payload.length = 42 * 129) : (encode (nonce, payload)).length = 5504 := by
  rw [length_encode, h]

end OptimalOTS.WeightedConstruction.NonceCodec

#print axioms OptimalOTS.WeightedConstruction.NonceCodec.decode_encode
#print axioms OptimalOTS.WeightedConstruction.NonceCodec.encode_injective
#print axioms OptimalOTS.WeightedConstruction.NonceCodec.encode_decode
#print axioms OptimalOTS.WeightedConstruction.NonceCodec.canonical_of_payload_positive
#print axioms OptimalOTS.WeightedConstruction.NonceCodec.signature86_length
