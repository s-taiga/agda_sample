FROM ayberkt/agda:v1

RUN cabal update
RUN cabal install Agda-2.6.3 --overwrite-policy=always

WORKDIR /root

RUN git clone --depth 1 --recurse-submodules --shallow-submodules https://github.com/plfa/plfa.github.io plfa
RUN mkdir -p ~/.agda
RUN cp ~/plfa/data/dotagda/* ~/.agda
