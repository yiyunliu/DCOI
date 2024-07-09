#!/usr/bin/sh
rm -rf artifact artifact.tar.zst
mkdir -p artifact/proofs
cd proofs
git archive --format=tar HEAD | tar -xf - --exclude=LICENSE --exclude=coq-pccomega.opam -C ../artifact/proofs
cd ..
tar caf artifact.tar.zst artifact 
