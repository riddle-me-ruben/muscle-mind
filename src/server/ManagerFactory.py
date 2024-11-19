from DatabaseManager import DatabaseManager
from QuizManager import QuizManager
from UserManager import UserManager
from DataAnalyticsManager import DataAnalyticsManager
from QuizRetrievalManager import QuizRetrievalManager
from QuizSubmissionManager import QuizSubmissionManager
from QuizCreationManager import QuizCreationManager
from flask import session

class ManagerFactory:
    def __init__(self, app):
        self.app = app
        self.db_manager = None

    def get_manager(self, manager_type):
        if manager_type == "DatabaseManager":
            if not self.db_manager:
                self.db_manager = DatabaseManager(self.app)
            return self.db_manager
        elif manager_type == "QuizManager":
            return QuizManager(self)
        elif manager_type == "UserManager":
            return UserManager(self.get_manager("DatabaseManager"), session)
        elif manager_type == "DataAnalyticsManager":
            return DataAnalyticsManager(self.get_manager("DatabaseManager"))
        elif manager_type == "QuizRetrievalManager":
            return QuizRetrievalManager(self.get_manager("DatabaseManager"),self.get_manager("DataAnalyticsManager"))
        elif manager_type == "QuizSubmissionManager":
            return QuizSubmissionManager(self.get_manager("DatabaseManager"),self.get_manager("QuizRetrievalManager"))
        elif manager_type == "QuizCreationManager":
            return QuizCreationManager(self.get_manager("DatabaseManager"))
        else:
            raise ValueError(f"Unknown manager type: {manager_type}")