import os

model_file_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)))


def _path(folder, file):
    """
    Internal method for generating path of files.
    :param folder: Folder.
    :param file: File containing model description.
    :return: Complete path to example file.
    """
    return os.path.join(model_file_dir, folder, file)
