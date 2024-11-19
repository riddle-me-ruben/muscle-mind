from DatabaseManager import DatabaseManager
from QuizManager import QuizManager
from UserManager import UserManager
from DataAnalyticsManager import DataAnalyticsManager
from QuizRetrievalManager import QuizRetrievalManager
from QuizSubmissionManager import QuizSubmissionManager
from QuizCreationManager import QuizCreationManager
from flask import session

"""
Description:
The ManagerFactory class provides a centralized way to create and manage various manager instances.
It uses a factory design pattern to abstract the creation logic and ensures efficient reuse of shared components, 
like the DatabaseManager, by caching instances where appropriate.

Semi-formal Notation:
/*@ requires app is a valid Flask instance (not null);
    @ ensures Provides methods to create and manage the following manager types:
    @   - "DatabaseManager": Manages database operations;
    @   - "QuizManager": Coordinates quiz-related tasks;
    @   - "UserManager": Manages user-related actions;
    @   - "DataAnalyticsManager": Retrieves and computes user analytics;
    @   - "QuizRetrievalManager": Fetches and organizes quiz data;
    @   - "QuizSubmissionManager": Handles quiz-taking and answer submission;
    @   - "QuizCreationManager": Manages the creation of quizzes;
@*/
"""
class ManagerFactory:

    """
    Description:
    Initializes the ManagerFactory instance and binds it to the given Flask application instance.
    The class caches the DatabaseManager instance to ensure only one database connection is created.

    Semi-formal Notation:
    /*@ requires app != null (a valid Flask application instance);
        @ ensures self.app == app;
        @ ensures self.db_manager is initialized as None for lazy instantiation;
    @*/
    """
    def __init__(self, app):
        self.app = app
        self.db_manager = None

    """
    Description:
    Returns the appropriate manager instance based on the provided manager_type.
    For the DatabaseManager, it caches the instance to avoid redundant initializations.
    For other managers, it creates new instances or uses dependencies as needed.

    Semi-formal Notation:
    /*@ requires manager_type is a valid string &&
        @ manager_type in {"DatabaseManager", "QuizManager", "UserManager", 
        @                   "DataAnalyticsManager", "QuizRetrievalManager", 
        @                   "QuizSubmissionManager", "QuizCreationManager"};
        @ ensures If manager_type == "DatabaseManager":
        @   - self.db_manager is initialized and returned (singleton instance);
        @ ensures If manager_type == "QuizManager":
        @   - Returns a new instance of QuizManager with dependencies resolved via factory;
        @ ensures If manager_type == "UserManager":
        @   - Returns a new instance of UserManager using DatabaseManager and session;
        @ ensures If manager_type == "DataAnalyticsManager":
        @   - Returns a new instance of DataAnalyticsManager using DatabaseManager;
        @ ensures If manager_type == "QuizRetrievalManager":
        @   - Returns a new instance of QuizRetrievalManager with DatabaseManager and DataAnalyticsManager;
        @ ensures If manager_type == "QuizSubmissionManager":
        @   - Returns a new instance of QuizSubmissionManager with DatabaseManager and QuizRetrievalManager;
        @ ensures If manager_type == "QuizCreationManager":
        @   - Returns a new instance of QuizCreationManager with DatabaseManager;
        @ ensures If manager_type is invalid:
        @   - Raises ValueError("Unknown manager type: <manager_type>");
    @*/
    """
    def get_manager(self, manager_type):
        match manager_type:
            case "DatabaseManager":
                if not self.db_manager:
                    self.db_manager = DatabaseManager(self.app)
                return self.db_manager
            case "QuizManager":
                return QuizManager(self)
            case "UserManager":
                return UserManager(self.get_manager("DatabaseManager"), session)
            case "DataAnalyticsManager":
                return DataAnalyticsManager(self.get_manager("DatabaseManager"))
            case "QuizRetrievalManager":
                return QuizRetrievalManager(self.get_manager("DatabaseManager"), self.get_manager("DataAnalyticsManager"))
            case "QuizSubmissionManager":
                return QuizSubmissionManager(self.get_manager("DatabaseManager"), self.get_manager("QuizRetrievalManager"))
            case "QuizCreationManager":
                return QuizCreationManager(self.get_manager("DatabaseManager"))
            case _:
                raise ValueError(f"Unknown manager type: {manager_type}")