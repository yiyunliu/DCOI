#!/usr/bin/sh
rm -rf artifact artifact.tar.zst
git archive --prefix='artifact/' --format=tar HEAD proofs | tar -xf - --exclude=LICENSE
tar cf artifact.tar.zst --zstd artifact
rm -r artifact
