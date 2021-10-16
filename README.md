# Semisimplicial
Semisimplicial types in Agda

This Agda code gives the first definition of (augmented) semisimplicial types which is expected to be correct in univalent type theory without any extended syntax.
We use a particular well-ordered filtration of the N-simplex, well-known in the simplicial complex community,
to inductively define an (augmented) N-truncated semisimplicial type X
by starting with an (augmented) (N-1)-truncated semisimplicial type XUnd,
and then defining the type of maps I --> X for each I in the filtration, by induction on I.
Ultimately, this yields a a definition of the type of maps from the boundary of the N -simplex to X;
We then define X in terms of a type of "fillers" for each such boundary map.

The filtration we use relies on defining binary natural numbers in a big-endian representation, in big-endian.agda.
This implementation is based on the little-endian implementation in https://github.com/agda/cubical/blob/master/Cubical/Data/BinNat/BinNat.agda by Anders Mortberg.

For now, see the code comments for further explanation.
