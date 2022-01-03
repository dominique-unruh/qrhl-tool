#!/usr/bin/python3

import readline, sys, atexit, pathlib, os, urllib.request, tempfile, subprocess, tarfile, shutil
from typing import List

release_version = "0.6"

def choices(question, choices):
    readline.set_completer(lambda text, state: (choices+[None])[state])
    print("\n")
    while True:
        answer = input(question+" ").lower()
        if answer in choices: return answer
        print("Please enter one of " + ", ".join(choices))

def read_path(question, check):
    def path_completer(f, i):
        dir = os.path.dirname(f)
        #print("DIR",f,dir)
        files = os.listdir("." if dir=="" else dir)
        #print("FILES",files)
        paths = [os.path.join(dir, file) for file in files]
        #print(paths)
        paths = [p for p in paths if p.startswith(f)] + [None]
        selected = paths[i]
        if selected and os.path.isdir(selected): selected = selected + "/"
        #print("SELECTED",selected)
        return selected

    readline.set_completer(path_completer)

    print("\n")
    while True:
        answer = input(question+" ")
        if answer == "": continue
        path = pathlib.Path(answer)
        if check(path): return path

        
def init_readline():
    readline.parse_and_bind("tab: complete")
    readline.set_completer_delims('')
    
    try: readline.read_history_file()
    except: pass

    atexit.register(readline.write_history_file)

    
def dialogue():
    global version, zip_url, isabelle_version, install_isabelle, isabelle_dir, install_afp, afp_dir, qrhl_dir
    
    ### qrhl-tool installation
    version = choices(f"Which version to install? R = release (v{release_version}); D = development snapshot.", ['d', 'r'])
    if version == 'd':
        isabelle_version = '2021-1'
    elif version == 'r':
        isabelle_version = '2019'
    else:
        sys.exit("Internal error")

    def check(f):
        if f.exists(): print("Directory already exist.")
        if not f.parent.exists(): print("Parent directory does not exist.")
        else: return True
    qrhl_dir = read_path(f"Where should qrhl-tool be installed? (Non-existing directory, e.g., /opt/qrhl-tool.)", check)


    ### Isabelle installation
    install_isabelle = choices(f"qrhl-tool needs Isabelle{isabelle_version}. Should I install it? Y = install, N = use existing installation.", ['y','n'])

    if install_isabelle == 'y':
        def check(f):
            if f.exists(): print("Directory already exists.")
            else: return True
        isabelle_dir = read_path(f"Where should Isabelle be installed? (Non-existing directory, e.g. /opt/Isabelle{isabelle_version})", check)

    else:
        def check(f):
            if not f.exists(): print("Directory does not exist.")
            elif not f.is_dir(): print("Not a directory.")
            elif not f.joinpath(f"Isabelle{isabelle_version}").is_file(): print(f"Not a valid Isabelle installation. Should contain the executable Isabelle{isabelle_version}")
            else: return True
        isabelle_dir = read_path(f"Where is Isabelle{isabelle_version} installed? (Existing directory, e.g. /opt/Isabelle{isabelle_version})", check)

        
    ### AFP installation
    install_afp = choices(f"qrhl-tool needs the Archive of Formal Proofs (AFP), a version compatible with Isabelle{isabelle_version}. Should I install it? Y = install, N = use existing installation.", ['y', 'n'])
    
    if install_afp == 'y':
        def check(f):
            if f.exists(): print("Directory already exists.")
            else: return True
        afp_dir = read_path(f"Where should the AFP be installed? (Non-existing directory, e.g. /opt/afp-{isabelle_version})", check)
    else:
        def check(f):
            if not f.exists(): print("Directory does not exist.")
            elif not f.is_dir(): print("Not a directory.")
            elif not f.joinpath(f"thys").is_dir(): print(f"Not a valid AFP installation. Should contain the directory thys.")
            else: return True
        afp_dir = read_path(f"Where is the AFP installed? (Existing directory, e.g. /opt/afp-{isabelle_version})", check)


def summary():
    print(f"""Configuration summary:

* Install {"development snapshot" if version=="d" else f"release {release_version}"}
* qrhl-tool directory: {qrhl_dir}
* Install Isabelle: {install_isabelle}
* Isabelle directory: {isabelle_dir}
* Install AFP: {install_afp}
* AFP directory: {afp_dir}

Press enter to start installation. (Ctrl-C to abort.)
""")
    input()



def do_install_isabelle():
    isabelle_urls = {'2021-1': 'https://isabelle.in.tum.de/dist/Isabelle2021-1_linux.tar.gz',
                     '2019': 'https://isabelle.in.tum.de/website-Isabelle2019/dist/Isabelle2019_linux.tar.gz'}
    url = isabelle_urls[isabelle_version]
    tgz_file = tempdir.joinpath("isabelle.tgz")
    
    print(f"Downloading Isabelle from {url}...")
    with urllib.request.urlopen(url) as response:
        with open(tgz_file, 'xb') as f:
            f.write(response.read())

    print(f"Extracting Isabelle to {isabelle_dir}...")
    os.mkdir(isabelle_dir)
    subprocess.check_call(["tar","-x","-f",tgz_file.absolute().as_posix(),
                           "-z","--strip-components","1"],
                          cwd = isabelle_dir)

    if isabelle_dir.joinpath(f"Isabelle{isabelle_version}").is_file():
        print("Isabelle successfully installed.")
    else:
        sys.exit(f"Isabelle installation failed. (Does not contain executable Isabelle{isabelle_version}.)")


def do_install_afp():
    afp_urls = {'2021-1': 'https://www.isa-afp.org/release/afp-current.tar.gz',
                '2019': 'https://downloads.sourceforge.net/project/afp/afp-Isabelle2019/afp-2019-08-19.tar.gz?download'}
    url = afp_urls[isabelle_version]
    tgz_file = tempdir.joinpath("afp.tgz")
    
    print(f"Downloading AFP from {url}...")
    with urllib.request.urlopen(url) as response:
        with open(tgz_file, 'xb') as f:
            f.write(response.read())

    print(f"Extracting AFP to {afp_dir}...")
    os.mkdir(afp_dir)
    subprocess.check_call(["tar","-x","-f",tgz_file.absolute().as_posix(),
                           "-z","--strip-components","1"],
                          cwd = afp_dir)
    
    if afp_dir.joinpath("thys").is_dir():
        print("AFP successfully installed.")
    else:
        sys.exit(f"AFP installation failed. (Does not contain directory thys.)")

        
def do_install_qrhl_tool():
    if version == 'd':
        url = 'https://nightly.link/dominique-unruh/qrhl-tool/workflows/test/master/qrhl.zip'
    elif version == 'r':
        url = f'https://github.com/dominique-unruh/qrhl-tool/releases/download/v{release_version}/qrhl.zip'
    else:
        sys.exit("Internal error")

    zip_file = tempdir.joinpath("qrhl.zip")

    print(f"Downloading qrhl-tool from {url}...")
    with urllib.request.urlopen(url) as response:
        with open(zip_file, 'xb') as f:
            f.write(response.read())

    print(f"Extracting qrhl-tool to {qrhl_dir}...")
    os.mkdir(qrhl_dir)
    subprocess.check_call(["unzip","-q","-d", qrhl_dir.as_posix(), zip_file.as_posix()])

    # Extracting nested ZIP if necessary
    content : List[pathlib.Path] = list(qrhl_dir.iterdir())
    if len(content)==1 and content[0].name.lower().endswith(".zip"):
        subprocess.check_call(["unzip","-q","-d", qrhl_dir.as_posix(), content[0].as_posix()])
        os.remove(content[0])

    # Moving stuff from the single subdir in the ZIP one level up
    content = list(qrhl_dir.iterdir())
    if len(content) == 0:
        sys.exit("qrhl-tool extraction failed. (Contains no files).")
    elif len(content) > 1:
        sys.exit("qrhl-tool extraction failed. (Contains multiple directories).")

    subdir = content[0]
    for f in subdir.iterdir():
        shutil.move(f, qrhl_dir)
    os.rmdir(subdir)

    if qrhl_dir.joinpath("bin").joinpath("qrhl").is_file():
        print("qrhl-tool successfully installed.")
    else:
        sys.exit(f"qrhl-tool installation failed. (Does not contain file bin/qrhl.)")


def config_qrhl_tool():
    conf_file = qrhl_dir.joinpath("qrhl-tool.conf")
    print(f"Configuring qrhl-tool (creating {conf_file.as_posix()})...")
    with open(conf_file, "wt") as f:
        f.write(f"""# Generated by the qrhl-tool installer. Change the paths of Isabelle and AFP if needed.

isabelle-home = {isabelle_dir}
afp-root = {afp_dir}
""")


def build_qrhl_tool():
    print("""

*************************************************    
Installation successful!

Building the Isabelle libraries of the qrhl-tool.
This can take a very long time.

It is safe to interrupt this step. (Ctrl-C)

But in that case, the long process will start the
first time you run the qrhl-tool.
*************************************************
""")
    build_qrhl = tempdir.joinpath("build.qrhl")
    bin_qrhl = qrhl_dir.joinpath("bin").joinpath("qrhl")
    with open(build_qrhl, "wt") as f:
        f.write("isabelle.\n")
    subprocess.check_call([bin_qrhl.as_posix(), build_qrhl.as_posix()], stdout=subprocess.DEVNULL)
    print("Build completed successfully.")

def install():
    global tempdir
    tempdir_object = tempfile.TemporaryDirectory(prefix="qrhl-tool-installer-")
    tempdir = pathlib.Path(tempdir_object.name)
    
    if install_isabelle == 'y': do_install_isabelle()
    if install_afp == 'y': do_install_afp()
    do_install_qrhl_tool()
    config_qrhl_tool()
    build_qrhl_tool()

    tempdir_object.cleanup()


# For testing purposes. Replace the call to dialogue() below by fake_dialogue() to skip the questions
def fake_dialogue():
    global version, zip_url, isabelle_version, install_isabelle, isabelle_dir, install_afp, afp_dir, qrhl_dir

    install_isabelle = 'n'
    install_afp = 'n'
    isabelle_version = '2021-1'
    version = 'd'
    isabelle_dir = pathlib.Path("/tmp/Isabelle2021-1")
    afp_dir = pathlib.Path("/opt/afp-2021-1")
    qrhl_dir = pathlib.Path("/tmp/qrhl")


init_readline()
dialogue()
summary()
install()
