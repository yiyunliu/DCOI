#!/usr/bin/sh
rm -rf artifact artifact.tar
git archive --prefix='artifact/' --format=tar HEAD proofs | tar -xf - --exclude=LICENSE
cd system-dcr/pi-forall
git archive --prefix='artifact/impl/' --format=tar HEAD | tar -xf - --exclude=.github --exclude=LICENSE  -C ../../
cd ../..
tar cf artifact.tar artifact
rm -r artifact
