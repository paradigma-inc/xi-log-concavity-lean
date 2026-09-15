# Shared eta batch evaluation

Starting from the certified state at grid index $k$, the batch advances the same outward-rounded root powers once per grid step. The $j$th emitted pair is exactly the accepted signed integer eta sum at index $k+j$, and the final state is exactly the accepted initialization at $k+n$. The proof is by induction using the established root-state successor identity. These identities justify reusing a checked final-state literal as the start of a later batch; they do not replace the required finite arithmetic checks.
