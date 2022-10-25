from setuptools import setup, find_packages
import sys

if sys.version_info[0] == 2:
    sys.exit('Sorry, Python 2.x is not supported')

setup(
    name='hyperprob',
    version='0.1.0',
    description='Model checker for Probabilistic Hyperproperties',
    url='https://github.com/TART-MSU/HyperProb',
    author='Oyendrila Dobe',
    author_email='oyendrila.dobe@gmail.com',
    packages=find_packages(),
    install_requires=[
        'stormpy>=1.6.3',
        'lark-parser',
        'z3-solver',
        'termcolor'
    ],
    python_requires='>=3.9',

    classifiers=[
        'Environment :: MacOS X',
        'Intended Audience :: Science/Research',
        'License :: OSI Approved :: MIT License',
        'Operating System :: MacOS :: MacOS X',
        'Operating System :: MacOS :: MacOS X',
        'Programming Language :: Python :: 3.9',
        'Topic :: Scientific/Engineering',
        'Topic :: Software Development :: Libraries :: Python Modules'
    ],
)
