#!/usr/bin/sh
set -xe

rm -rf artifact artifact.tar
git archive --prefix='artifact/' --format=tar HEAD proofs | tar -xf -
cd system-dcr/pi-forall
git archive --prefix='artifact/impl/' --format=tar HEAD | tar -xf - --exclude=.github  -C ../../
cd ../..
cp reference-appendix.pdf artifact/
tar --create --numeric-owner --file artifact.tar artifact
rm -r artifact
