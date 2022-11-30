FROM makarius/isabelle:Isabelle2021-1

# Install dependencies
USER root
RUN apt-get -y update && apt-get install -y default-jre && apt-get clean
USER isabelle

# Build session HOL-Analysis
RUN Isabelle/bin/isabelle build -b HOL-Analysis

# Install and configure AFP
RUN mkdir afp && (cd afp && curl https://www.isa-afp.org/release/afp-current.tar.gz | tar -x -z --strip-components 1) && echo "$PWD/afp/thys" >> Isabelle/ROOTS

# Build session Complex_Bounded_Operators
RUN Isabelle/bin/isabelle build -b Complex_Bounded_Operators

# Install and configure qrhl-tool
COPY --chown=isabelle qrhl.zip /tmp/qrhl.zip
RUN unzip /tmp/qrhl.zip && rm /tmp/qrhl.zip && mv qrhl-snapshot qrhl && echo "isabelle-home = $PWD/Isabelle" > ~/.qrhl-tool.conf

# Build sessions of qrhl-tool
RUN qrhl/bin/qrhl --build

# Connect image to github repository
LABEL org.opencontainers.image.source https://github.com/dominique-unruh/qrhl-tool

ENTRYPOINT ["qrhl/bin/qrhl"]
