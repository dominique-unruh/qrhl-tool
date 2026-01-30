FROM archlinux:latest-cached

RUN bash -ex <<EOT  # Update package keys
pacman-key --init
pacman-key --populate archlinux
pacman-key --refresh-keys
EOT

RUN bash -ex <<EOT  # Install dependencies
pacman -Sy --noconfirm wget file sudo fontconfig git gnupg curl sbt ttf-dejavu pcre2 inetutils make
pacman -Sc
EOT

RUN useradd -m user

WORKDIR /home/user

ARG ISABELLE_VERSION

RUN bash -ex <<EOT  # Download Isabelle
test -n "${ISABELLE_VERSION}"
export ISABELLE_URL="https://isabelle.in.tum.de/website-Isabelle${ISABELLE_VERSION}/dist/Isabelle${ISABELLE_VERSION}_linux.tar.gz"
echo "Downloading \$ISABELLE_URL"
curl "\$ISABELLE_URL" > /tmp/isabelle.tgz
mkdir /opt/Isabelle
cd /opt/Isabelle
tar -x --strip-components=1 -f /tmp/isabelle.tgz
rm /tmp/isabelle.tgz
EOT

USER user

RUN bash -ex <<EOT  # Build HOL-Analysis
/opt/Isabelle/bin/isabelle build -b -v HOL-Analysis
EOT

USER root

RUN bash -ex <<EOT  # Download AFP
case \$ISABELLE_VERSION in
  2025-2|2025-1) AFP_DATE=2025-12-19;;
  *) echo "Don't know AFP release date for Isabelle\$ISABELLE_VERSION"; exit 1;;
esac
wget -q "https://www.isa-afp.org/release/afp-\$AFP_DATE.tar.gz" -O /tmp/afp.tgz
mkdir /opt/afp
cd /opt/afp
tar -x --strip-components=1 -f /tmp/afp.tgz
chmod -R a+rX /opt/afp
ls -lh /opt/afp
EOT

USER user

#RUN bash -ex <<EOT  # Config AFP & build Registers
#ls -lh /opt/afp/thys
#echo /opt/afp/thys >> .isabelle/Isabelle${ISABELLE_VERSION}/ROOTS
#/opt/Isabelle/bin/isabelle build -b -v Registers -d /opt/afp/thys  # Build Registers
#EOT

RUN /opt/Isabelle/bin/isabelle build -b -d /opt/afp/thys -v Registers  # Build Registers

ARG JAVA_VERSION

USER root

RUN bash -ex <<EOT  # Install Java ${JAVA_VERSION} & sbt
pacman -S --noconfirm jdk${JAVA_VERSION}-openjdk
archlinux-java set java-${JAVA_VERSION}-openjdk
java -version
pacman -Sc
EOT

USER user

# Copy just the files needed for build.sbt to fetch all dependencies
COPY --chown=user --parents all-files/./build.sbt all-files/./project/build.properties all-files/./project/plugins.sbt \
    all-files/./scala-isabelle/build.sbt all-files/./scala-isabelle/project/build.properties all-files/./scala-isabelle/project/plugins.sbt \
    all-files/./src/main/resources/qrhl/isabellex/isabelleVersion all-files/./version \
    qrhl-tool/

WORKDIR qrhl-tool
RUN sbt compile  # sbt prefetch

# Copy just the files needed to build the Isabelle QRHL-Prerequisites session
COPY --chown=user --parents all-files/./isabelle-thys/ROOT  all-files/./isabelle-thys/fake-session-dir qrhl-tool/
WORKDIR qrhl-tool
RUN /opt/Isabelle/bin/isabelle build -b -v -d /opt/afp/thys -d isabelle-thys QRHL-Prerequisites

# Doesn't work, it's rebuilt anyway later for some reason.
## Copy just the files needed to build the Isabelle QRHL-Scala session
#COPY --chown=user --parents all-files/./isabelle-thys .
#RUN /opt/Isabelle/bin/isabelle build -b -v -d /opt/afp/thys -d isabelle-thys QRHL-Scala

WORKDIR /home/user

RUN rm -rf qrhl-tool

COPY --chown=user all-files qrhl-tool

WORKDIR qrhl-tool
RUN bash -ex <<EOT  # Testing
cat << END >> qrhl-tool.conf
isabelle-home = /opt/Isabelle
afp-root = /opt/afp
END
mkdir -p target/test-reports-html
sbt "testOnly -- -h target/test-reports-html" |& tee target/test-reports-html/raw-output.txt
echo -n "\${PIPESTATUS[0]}" >target/test-reports-html/return-code.txt
make qrhl.zip
mv qrhl.zip target/test-reports/
EOT
