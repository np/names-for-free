Security properties using games and probabilities
  Examples of games
    Either
      PRG + 1 time SS
      OTP and Stream Cipher
    Or
      DDH + PubKey SS
      El Gamal (OTP likeness)
  Advantage
  Security statement
  Reduction
  Recap of theories involved (game, information, number, complexity, probability)

Formal counting
  Randomized programs...
    as deterministic functions with an extra argument
      advantages
      limitations
  Counting Bits
  Summing Fin, Bits, Products
    properties of summations
  Small program equivalences:
    - Picking randomness in different ways:
        - x ← ?, y ← ?, f x y
        - y ← ?, x ← ?, f x y
    - Distribution preserving operations (OTP-likeness):
        - (x,y) ← ?, x ⊕ y
        - x ← ?, x
        - x ← ?, y ← …, x ⊛ y
  bijections
  ...

Cost models?

Circuits?

Case studies
  1 time SS Game
  PRG Game
  OTP
  pre;E;post
  elgamal
  schnorr sig?
  ZK IP
  hash?

