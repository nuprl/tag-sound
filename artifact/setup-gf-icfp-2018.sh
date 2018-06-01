#!/bin/bash

ARTIFACT=gf-icfp-2018

[ -d ${ARTIFACT} ] || git clone https://github.com/nuprl/tag-sound.git ${ARTIFACT}

make -C ${ARTIFACT} install
