import sys

from setuptools import setup

if sys.version_info[0] == 2:
    sys.exit("Sorry, Python 2 is not supported.")


setup(
    name='HyperOnMDPtool',
    version='1.0.0',
    packages=[''],
    url='https://github.com/oyendrila-dobe/HyperOnMDPtool',
    license='MIT',
    author='oyendriladobe',
    author_email='dobeoyen@msu.edu',
    description='HyperOnMDP - Verifying probabilistic hyperproperties on Markov Decision Processes',
    long_description="HyperOnMDP is a library and script-collection for methods handling verification of probabilistic hyperproperties in Markov decision processes",
    install_requires=[ 'pycarl>=2.0.3', 'lark-parser', 'z3-solver'],
    tests_require=[],
    extras_require={
        'stormpy': ["stormpy"]
    },
    package_data={},
    scripts=[
        'scripts/source.py',
        'files.py']
)
