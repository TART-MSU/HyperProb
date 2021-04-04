import os

testfile_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "HyperOnMDP/model_files")


def _path(folder, subfolder, file):
    """
    Internal method for simpler listing of examples.
    :param folder: Folder.
    :param file: Example file.
    :return: Complete path to example file.
    """
    return os.path.join(testfile_dir, folder, subfolder, file)
