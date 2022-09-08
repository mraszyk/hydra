FROM ubuntu:22.04

RUN apt-get update
RUN apt-get upgrade -y
RUN DEBIAN_FRONTEND=noninteractive apt-get install --no-install-recommends -y bc bison ca-certificates clang flex git gnuplot libboost-dev libgmp3-dev libssl-dev locales make m4 opam python3 python3-pip vim

RUN adduser --disabled-password --gecos "" hydra
RUN locale-gen en_US.UTF-8 &&\
    echo "export LANG=en_US.UTF-8 LANGUAGE=en_US.en LC_ALL=en_US.UTF-8" >> /home/hydra/.bashrc

RUN pip3 install antlr4-python3-runtime ply pyyaml setuptools wheel

USER hydra
RUN opam init -y --disable-sandboxing
RUN opam install -y ocamlbuild ocamlfind ctypes dune dune-build-info safa menhir qcheck zarith

ENV WDIR /home/hydra
WORKDIR ${WDIR}

# Aerial
RUN git clone https://bitbucket.org/traytel/aerial.git
RUN eval `opam config env`; make -C aerial

# MonPoly/VeriMon
RUN git clone https://bitbucket.org/jshs/monpoly.git
RUN eval `opam config env`; cd monpoly; dune build --release

# Reelay
RUN git clone https://github.com/mraszyk/reelay-codegen.git
RUN cd reelay-codegen; python3 setup.py build; cp scripts/reelay reelay.py

ADD . ${WDIR}
USER root
RUN chmod 755 /home/hydra
RUN chown -R hydra:hydra *
USER hydra

# HYDRA/VYDRA
RUN eval `opam config env`; make -C src

# evaluation
RUN make -C evaluation

USER root
RUN echo "su - hydra" >> /root/.bashrc
