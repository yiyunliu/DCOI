#!/usr/bin/sh
rm -rf artifact artifact.tar
git archive --prefix='artifact/' --format=tar HEAD proofs | tar -xf - --exclude=LICENSE
tar cf artifact.tar artifact
rm -r artifact
